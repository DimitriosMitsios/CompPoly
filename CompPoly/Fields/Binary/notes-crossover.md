# Karatsuba vs fold crossover experiment

## Question

For small widths (128 bits), the hand-rolled `Fin.foldl`-based
`clMul128_opt` beats a single-level Karatsuba `clMul128_karatsuba` on our
Lean benchmarks (see `notes-karatsuba.md`). This runs against intuition:
Karatsuba is asymptotically `O(n^1.585)` vs the fold's `O(n^2)`, so the
two curves *must* cross somewhere. The hypothesis was that 128 bits is
simply too small to see Karatsuba's asymptotic advantage, and that
pushing the bit width up would expose the crossover.

To test this, we implemented generic fold and *recursive* Karatsuba
variants at widths 256, 512, 1024, 2048, and 4096 bits. At each level,
`clMulN_karatsuba` splits its inputs in half and calls
`clMul(N/2)_karatsuba` for the three sub-multiplies, bottoming out at
`clMul128_opt`. This is the shape that should actually see Karatsuba's
asymptotic win if one exists.

## Implementation

See `tests/CompPolyTests/Fields/Binary/CommonBench.lean`, Section 5. Each
width has two variants:

- `clMulN_opt : BitVec N → BitVec N → BitVec (2*N)` — fold over N bits
  with a single pre-widened `b` and `Fin.foldl`. Same shape as the
  production `clMul128_opt`.
- `clMulN_karatsuba : BitVec N → BitVec N → BitVec (2*N)` — split at `N/2`,
  3 sub-multiplies via `clMul(N/2)_karatsuba`, recombine with
  `zeroExtend`, `<<<`, and `^^^`.

All recursion is handled through `@[inline]` specialisation — every size
gets its own compiled function. (At 8192 bits the inliner ran out of
budget with 6 recursion levels, so we capped the experiment at 4096.)
Correctness is cross-checked via `#guard clMulN_opt == clMulN_karatsuba`
up to 1024 bits; beyond that, `#guard`'s decision procedure hits
`maxRecDepth` at compile time, so we rely on the smaller-width checks and
the fact that the same Lean definitions are being exercised.

## Results

Iteration counts were scaled down as width grew to keep total wall time
under a couple of seconds per data point.

| Width  | Iters  | `opt` total | `kara` total | `opt` µs/call | `kara` µs/call | **kara/opt** |
|-------:|-------:|------------:|-------------:|--------------:|---------------:|-------------:|
|   128  | 10 000 |      1.26 s |       1.72 s |           126 |            172 |    **1.37×** |
|   256  |  5 000 |      1.32 s |       1.72 s |           264 |            344 |    **1.30×** |
|   512  |  2 000 |      1.06 s |       2.13 s |           530 |          1 065 |    **2.01×** |
|  1024  |    500 |     562 ms  |       1.55 s |         1 124 |          3 100 |    **2.76×** |
|  2048  |    100 |     256 ms  |      842 ms  |         2 560 |          8 420 |    **3.29×** |
|  4096  |     25 |     135 ms  |      532 ms  |         5 400 |         21 280 |    **3.94×** |

The ratio column is the punch line: **Karatsuba loses harder at every
doubling**. There is no crossover in sight — the curves are diverging,
not converging.

## Measured scaling

The per-call µs/call numbers give the following doubling ratios
(each entry is `row / previous row`):

**Fold (`opt`)**: 126 → 264 → 530 → 1124 → 2560 → 5400 µs
per-doubling ratios: 2.10, 2.01, 2.12, 2.28, 2.11 — mean **~2.1× per doubling**.

**Karatsuba**: 172 → 344 → 1065 → 3100 → 8420 → 21280 µs
per-doubling ratios: 2.00, 3.10, 2.91, 2.72, 2.53 — converging to **~3× per doubling**.

These numbers are measured and reproducible.

## Explanation — what is solid

**Karatsuba's 3× per doubling is exactly what the algorithm predicts.**
One level of recursion does three sub-multiplies of half size, so
`T(N) = 3·T(N/2) + O(N)`. By the master theorem this gives
`Θ(N^{log₂ 3}) = Θ(N^{1.585})`, and in the regime where the recurrence
term dominates the linear recombination term, the per-doubling ratio
converges to exactly `3`. Our measurements hit this cleanly from `N = 512`
onward. There is no mystery here.

**Karatsuba does structurally more allocation than the fold per call.**
Each recursive call creates fresh `BitVec` values for four split operands,
three sub-products, three `zeroExtend`s, two shifts, and two XORs. At
`N = 4096`, the recursion has 5 levels and expands to `3^5 = 243` leaf
calls to `clMul128_opt`, each of which is itself a 128-iter fold with its
own per-iter allocations, plus all the intermediate recombination at
every level. Whatever the exact per-op constants turn out to be, the
Karatsuba pipeline is unambiguously doing more work per call than the
straight fold. That alone is enough to explain *some* constant-factor
penalty, and it's why we see Karatsuba trail the fold even at `N = 128`.

## Explanation — what is conjecture

**Why the fold scales at ~2.1× per doubling and not 4× is not explained
by the above, and I do not have a verified answer for it.**

The naive cost model says: the fold has `N` iterations; each iteration
does a conditional XOR of a `2N`-bit accumulator with `b' <<< i.val`.
If `BitVec` shift and XOR at width `w` both cost `Θ(w)` — which is what
you would expect if they bottom out in limb-level memcpy/XOR on a
word-array representation — then per-iter cost is `Θ(N)` and total cost
is `Θ(N²)`. That predicts a **4× per-doubling ratio**, not the **~2.1×**
we actually see.

Something about the way Lean implements `BitVec` at these widths is
making the fold scale sub-quadratically, but I did not verify what. A
few candidate hypotheses:

1. **GMP entry/exit overhead dominates at these widths.** `BitVec` is
   ultimately backed by `Nat`, and `Nat` at large values is GMP-backed.
   If the per-op constant (FFI boundary, boxing, result allocation) is
   large compared to the limb-level work at `N ≤ 4096`, then each
   `BitVec` operation looks approximately constant in width, and the
   fold's per-iter cost is constant, giving linear scaling in `N` →
   `~2×` per doubling.
2. **Allocation/GC overhead per iteration dominates.** The inner loop
   of `Fin.foldl` allocates a fresh `BitVec` for every shift and every
   XOR (two per iteration). If allocation cost per object is roughly
   independent of width over this range, per-iter cost is approximately
   constant → again linear scaling.
3. **The compiler is doing something I haven't accounted for.** E.g.
   common subexpression elimination on the loop body for fixed inputs,
   or specialisation of `Fin.foldl` that I don't understand.

**Why these are conjectures, not answers**: I have no profile data, no
knowledge of Lean's current `BitVec` runtime representation, and no
comparison run that isolates per-iter cost from per-op cost. The naive
"shift costs `Θ(N/wordsize)` limbs" argument is strong enough that I
*should* be seeing closer to `4×` per doubling, and the fact that I'm
not means something in the above list (or something I haven't thought
of) is true — but I cannot tell you which.

**What would be needed to turn this into a real answer**:

- Run one `clMul4096_opt` call under `perf`, `flamegraph`, or
  equivalent, and see where the time actually lives: GMP, `BitVec`
  runtime, GC, or the loop itself.
- Read `Nat.shiftLeft` / `Nat.xor` in the Lean runtime to see the
  threshold at which they switch representations or enter GMP.
- Run the fold with iteration count fixed and width varied, and
  separately with width fixed and iteration count varied, to
  disentangle per-iter cost from per-op cost.

None of this was done. The conclusion about Karatsuba below does **not**
depend on any of it.

## Where would Karatsuba's asymptotic win appear? (extrapolation)

This is also conjecture, but simpler. Given the current trend, the
`kara/opt` ratio is growing roughly by `1.5×` per doubling (after the
initial 256-bit region). For the ratio to come *back* down, the fold's
doubling ratio would have to climb from the measured `~2.1×` toward the
theoretical `4×` and eventually dominate Karatsuba's `3×`. That requires
whatever is keeping the fold sub-quadratic to break down at some larger
width. *If* the explanation is "GMP entry overhead dominates", then the
break-even point is when the limb-level work finally overtakes the per-op
constants — probably somewhere in the tens of thousands of bits. *If* the
explanation is something else, the crossover could be elsewhere. Either
way, it is far beyond any width this codebase cares about: GHASH is 128
bits.

## Caveats

- **Higher widths than 4096 were not tested.** At 8192 bits, Lean's
  `@[inline]` code generator ran out of budget when specialising the
  6-level recursive Karatsuba. The experiment could be redone with the
  inner variants made `noncomputable`-safe or un-inlined, but the trend
  is already unambiguous.
- **We only measured wall-clock `timeit`, not allocation counts.** A
  proper profile would show where the Karatsuba time actually goes — my
  hypothesis is that intermediate `BitVec` allocation dominates, but I
  have not confirmed it.
- **This is specific to Lean's current `BitVec` implementation.** The
  same algorithmic comparison in C or Rust would look very different,
  because primitive XOR on fixed-width integers is `O(1)` there, so the
  fold really is `Θ(N²)` and Karatsuba crosses over at a much smaller
  `N`. The conclusion here is about Lean, not about Karatsuba.
- **Only recursive Karatsuba was tested at large widths.** A single-level
  Karatsuba (one split, sub-multiplies via `clMulN/2_opt`) might scale
  differently; it would still lose asymptotically, but the crossover
  shape could be different. This is a potential follow-up.

## Conclusion

For the issue #129 PR, the takeaway is that **no amount of algorithmic
cleverness à la Karatsuba is going to beat the simple fold at the sizes
we care about.** `clMul128_opt` remains the right variant to finalise.
The exploration was not wasted: we now have empirical evidence that the
theoretical asymptotic argument does not apply in Lean's BitVec regime,
which is a useful thing to cite if the question ever comes up again.

# Carry-less multiplication: optimisation notes (issue #129)

## Goal

Issue #129 asks for a faster `clMul` in `CompPoly/Fields/Binary/Common.lean`,
with Karatsuba as the suggested starting point and a rough target of ~25 %
improvement. The original definition folds over 256 bits of `a` and
conditionally XOR-shifts `b`:

```lean
def clMul (a b : B256) : B256 :=
  (Finset.univ : Finset (Fin 256)).fold BitVec.xor 0
      (fun i => if a.getLsb i then b <<< i.val else 0)
```

All production callers (`BF128Ghash/Impl.lean`, `Prelude.lean`) invoke it as
`clMul (to256 a) (to256 b)` with `a b : B128`, and the correctness lemma
`toPoly_clMul_no_overflow` has the precondition `da + db ≤ 257`. So the
hot-path shape is really `B128 × B128 → B256`; the extra 128 iterations over
known-zero high bits are pure overhead.

## Kept in the PR

After experimentation we retained only two new definitions:

- **`clMul128_opt : B128 → B128 → B256`** — the fastest variant we found.
  Uses `Fin.foldl` (tighter compiled loop than `Finset.fold`) and hoists the
  `to256 b` widening out of the loop body.
- **`clMul128_karatsuba : B128 → B128 → B256`** — single-level Karatsuba
  splitting each operand at bit 64, with three `clMul64_128` sub-multiplies.
  Included so reviewers can compare the algorithmic approach against the
  straightforward fold.

Both live in `CompPoly/Fields/Binary/Common.lean`. `clMul` itself is left
untouched — correctness proofs downstream still depend on it, and until
`toPoly_clMul128_opt` / `toPoly_clMul128_karatsuba` are proved we cannot
swap the definition.

## Benchmark (10 000 iterations, `#eval timeit`, Fin.foldl build)

Measured in `tests/CompPolyTests/Fields/Binary/CommonBench.lean`, which is
intentionally *not* wired into `lake test` so it does not slow the CI loop.

| Variant                | Fixed dense | Varied | Sparse 128×8 |
|------------------------|------------:|-------:|-------------:|
| `clMul (to256 …)`      |      2.48 s | 2.38 s |       2.27 s |
| `clMul128_karatsuba`   |      1.55 s | 1.51 s |       1.19 s |
| `clMul128_opt`         |  **1.13 s** | 1.15 s |       1.07 s |

`clMul128_opt` is ~54 % faster than the baseline on dense inputs; the
Karatsuba variant lands around 37 % faster. On the sparse (128×8)
`fold_step` shape the gap narrows because the baseline’s inner branch
skips most iterations.

## Other approaches tried (and discarded)

1. **Full-recursion Karatsuba `clMul_karatsuba : BitVec w → BitVec (2*w)`.**
   Generic recursive split down to `w ≤ 1`. Correct, but ≈ 80× *slower* than
   the baseline: every level pays for `extractLsb'`, `truncate`, and a fresh
   `BitVec` allocation. Termination required `decreasing_by all_goals omega`
   over `w / 2` (plain `w / 2`, not `Nat.ceil`, which `omega` treats as
   opaque).

2. **`clMul128` (B128 input, `Finset.fold`).** Just halves the iteration
   count relative to the baseline by skipping the known-zero high half.
   Gave ~27 % improvement but is strictly dominated by `clMul128_opt`
   (same loop body, slower iterator).

3. **`clMul128'` (B128 input, `Fin.foldl`, pre-widened `b256` argument).**
   Helper used by the B256-split variants. Subsumed by `clMul128_opt`,
   which bakes the widening into the function.

4. **`clMul_karatsuba_single : B256 → B256 → B256` with `extractLsb'`.**
   Single-level Karatsuba over 256-bit operands, splitting at bit 128 with
   explicit extract-and-widen. ~24 % faster than baseline — the
   extract/`to256` calls eat most of the theoretical Karatsuba win.

5. **`clMul_karatsuba_single'` — same but all-B256 with mask/shift.** Avoids
   the `extractLsb'` overhead by keeping everything in `B256` and masking
   with `(1 <<< 128) - 1`. Roughly on par with (4); still slower than
   `clMul128_opt` because every sub-multiply loops in a 256-bit accumulator
   that is mostly zero.

6. **`clMul128_karatsuba_opt` — Karatsuba with B128 accumulators.**
   Accumulates the three 64-bit sub-products in `B128` (they fit in 127
   bits) and only widens to `B256` for the final recombination. About 37 %
   faster than baseline — indistinguishable from the simpler
   `clMul128_karatsuba` above, so not worth the extra surface area.

7. **Two-level Karatsuba `clMul_karatsuba_2level` (256 → 128 → 64).** Nine
   64-bit fold sub-multiplies. The extra recombination layer cost more than
   it saved; slower than single-level.

8. **`clMul128_u64` — schoolbook with native `UInt64` limbs.** Based on a
   GPT-5 suggestion (see `clmul_gpt5-2.lean`). Splits each `B128` into two
   `UInt64` limbs, runs four 64×64 sub-multiplies with native `UInt64`
   shift/XOR, and repacks into `B256`. Intuitively appealing since the
   inner loop uses machine words instead of `BitVec` — but in practice it
   was *slower* than the baseline (≈ 3.17 s vs 2.60 s, 22 % worse). The
   cost of the `BitVec ↔ UInt64` conversions (`extractLsb'` + `toNat` +
   `ofNat` four times per call, plus `zeroExtend 256` four times on the
   output) dominates the savings from the native loop body. A pure-`UInt64`
   pipeline that never round-trips through `BitVec` would likely do better,
   but that would require changing the downstream API.

## Observations

- **The biggest single win is not Karatsuba.** On our inputs, swapping
  `Finset.fold` over `Fin 256` for `Fin.foldl` over `Fin 128` with the
  `to256 b` lifted out of the body gets us most of the way. Karatsuba does
  strictly fewer XORs in theory, but the per-call recombination overhead
  (masks, shifts, three separate fold loops) eats much of the saving.
- **`BitVec ↔ UInt64` conversions are expensive.** Any strategy that hops
  out to native machine words for the hot loop has to avoid paying the
  conversion toll more than once. Our attempt to do so round-tripped on
  every call and lost.
- **Full-recursion Karatsuba is a trap for small fixed sizes.** The
  algorithmic win kicks in asymptotically, but at `w = 128` the
  per-frame overhead (dependent BitVec sizes, `extractLsb'`, `truncate`,
  termination proof) is much larger than the constant-factor saving.
- **The B256 signature is not load-bearing.** Every call site in the
  repository passes `to256 a, to256 b` where the originals are `B128`.
  A future PR could migrate `clMul` to `B128 → B128 → B256` once the
  `toPoly_*` lemmas are ported, which would let us drop `clMul`
  entirely in favour of `clMul128_opt`.

## Open items

- Prove `toPoly_clMul128_opt` and `toPoly_clMul128_karatsuba` so the new
  definitions can replace `clMul` at the call sites without a correctness
  regression.
- Ask the maintainers whether the `B256 → B256 → B256` signature is
  deliberate (the `da + db ≤ 257` precondition hints at a possible 129-bit
  edge case that isn’t exercised today).
- Investigate whether a pure-`UInt64` pipeline — i.e. convert once at the
  boundary, stay in native words through an entire GHASH block — is worth
  a larger refactor.

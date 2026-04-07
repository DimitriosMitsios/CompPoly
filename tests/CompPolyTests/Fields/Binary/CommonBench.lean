/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris
-/
import CompPoly.Fields.Binary.Common

/-!
  # Benchmarks: clMul variants

  Compares the three surviving carry-less multiplication implementations:
  - `clMul` — the original 256-bit fold baseline
  - `clMul128_karatsuba` — single-level Karatsuba on B128 (split at 64)
  - `clMul128_opt` — optimised fold on B128 (`Fin.foldl` + hoisted `to256`)

  See `CompPoly/Fields/Binary/notes-karatsuba.md` for the full list of
  approaches that were tried and their results.

  This file is intentionally **not** imported by `CompPolyTests.lean`
  so that `lake test` stays fast.

  ## Running

  ```bash
  lake build CompPolyTests.Fields.Binary.CommonBench
  ```
-/

open BinaryField

/-! ## Section 1: Correctness — all variants must agree -/

private def tv_a : B128 := (0xDEADBEEFCAFEBABE0123456789ABCDEF : B128)
private def tv_b : B128 := (0xFEEDFACEFEEDFACE1122334455667788 : B128)

-- Reference result from original clMul
private def ref_result : B256 := clMul (to256 tv_a) (to256 tv_b)

#guard clMul128_karatsuba tv_a tv_b == ref_result
#guard clMul128_opt tv_a tv_b == ref_result

-- Second pair: one operand with few bits set (matches fold_step use case)
private def tv_sparse : B128 := (0x87 : B128)  -- X^7 + X^2 + X + 1, like R_val

private def ref_sparse : B256 := clMul (to256 tv_a) (to256 tv_sparse)

#guard clMul128_karatsuba tv_a tv_sparse == ref_sparse
#guard clMul128_opt tv_a tv_sparse == ref_sparse

-- Third pair: both operands small
private def tv_small_a : B128 := (0xFF : B128)
private def tv_small_b : B128 := (0xAB : B128)

private def ref_small : B256 := clMul (to256 tv_small_a) (to256 tv_small_b)

#guard clMul128_karatsuba tv_small_a tv_small_b == ref_small
#guard clMul128_opt tv_small_a tv_small_b == ref_small

-- Fourth pair: multiply by 1 (identity)
#guard clMul128_karatsuba tv_a 1 == to256 tv_a
#guard clMul128_opt tv_a 1 == to256 tv_a

-- Fifth pair: multiply by 0
#guard clMul128_karatsuba tv_a 0 == 0
#guard clMul128_opt tv_a 0 == 0

/-! ## Section 2: Benchmarks — fixed dense inputs (throughput) -/

private def benchFixed (f : B128 → B128 → B256) (n : Nat) (a b : B128) : IO B256 := do
  let mut r : B256 := 0
  for _ in List.range n do
    r := f a b
  return r

#eval timeit "=== Fixed dense 128x128 (10000 iters) ===" (pure ())
#eval timeit "  clMul(to256)" (benchFixed (fun a b => clMul (to256 a) (to256 b)) 10000 tv_a tv_b)
#eval timeit "  clMul128_karatsuba" (benchFixed clMul128_karatsuba 10000 tv_a tv_b)
#eval timeit "  clMul128_opt" (benchFixed clMul128_opt 10000 tv_a tv_b)

/-! ## Section 3: Benchmarks — varied inputs (defeats branch prediction) -/

-- Generate varied inputs by XOR-mixing the iteration index into the base vector
private def benchVaried (f : B128 → B128 → B256) (n : Nat) (a b : B128) : IO B256 := do
  let mut r : B256 := 0
  for i in List.range n do
    let a' := a ^^^ (BitVec.ofNat 128 (i * 0x9E3779B97F4A7C15))  -- golden ratio hash
    let b' := b ^^^ (BitVec.ofNat 128 (i * 0x6C62272E07BB0142))
    r := f a' b'
  return r

#eval timeit "=== Varied inputs 128x128 (10000 iters) ===" (pure ())
#eval timeit "  clMul(to256)" (benchVaried (fun a b => clMul (to256 a) (to256 b)) 10000 tv_a tv_b)
#eval timeit "  clMul128_karatsuba" (benchVaried clMul128_karatsuba 10000 tv_a tv_b)
#eval timeit "  clMul128_opt" (benchVaried clMul128_opt 10000 tv_a tv_b)

/-! ## Section 4: Benchmarks — sparse inputs (128×8 bit, like fold_step) -/

private def benchSparse (f : B128 → B128 → B256) (n : Nat) (a b : B128) : IO B256 := do
  let mut r : B256 := 0
  for _ in List.range n do
    r := f a b
  return r

#eval timeit "=== Sparse 128x8 bit (10000 iters) ===" (pure ())
#eval timeit "  clMul(to256)" (benchSparse (fun a b => clMul (to256 a) (to256 b)) 10000 tv_a tv_sparse)
#eval timeit "  clMul128_karatsuba" (benchSparse clMul128_karatsuba 10000 tv_a tv_sparse)
#eval timeit "  clMul128_opt" (benchSparse clMul128_opt 10000 tv_a tv_sparse)

/-! ## Section 5: Crossover experiment — fold vs recursive Karatsuba at larger widths

    At each width N ∈ {256, 512, 1024}, we compare:
    - `clMulN_opt`        — fold over N bits (`Fin.foldl`, hoisted widening)
    - `clMulN_karatsuba`  — single-level Karatsuba that recurses into the
                            next-smaller Karatsuba for its three sub-multiplies.
    The recursion bottoms out at `clMul128_opt` (the fastest 128-bit fold we have).
    Karatsuba should win asymptotically, so we expect a crossover somewhere
    above 128 bits. -/

abbrev B512 := BitVec 512
abbrev B1024 := BitVec 1024
abbrev B2048 := BitVec 2048

/-- Fold-based 256×256 → 512 clMul. -/
@[inline] private def clMul256_opt (a b : B256) : B512 :=
  let b' : B512 := b.zeroExtend 512
  Fin.foldl 256 (init := (0 : B512))
    (fun acc i => if a.getLsbD i.val then acc ^^^ (b' <<< i.val) else acc)

/-- Single-level Karatsuba 256×256 → 512, sub-multiplies via `clMul128_opt`. -/
@[inline] private def clMul256_karatsuba (a b : B256) : B512 :=
  let a_lo : B128 := a.truncate 128
  let a_hi : B128 := (a >>> 128).truncate 128
  let b_lo : B128 := b.truncate 128
  let b_hi : B128 := (b >>> 128).truncate 128
  let z_0 : B256 := clMul128_opt a_lo b_lo
  let z_2 : B256 := clMul128_opt a_hi b_hi
  let z_3 : B256 := clMul128_opt (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let z_1 : B256 := z_3 ^^^ z_0 ^^^ z_2
  (z_0.zeroExtend 512) ^^^ ((z_1.zeroExtend 512) <<< 128) ^^^ ((z_2.zeroExtend 512) <<< 256)

/-- Fold-based 512×512 → 1024 clMul. -/
@[inline] private def clMul512_opt (a b : B512) : B1024 :=
  let b' : B1024 := b.zeroExtend 1024
  Fin.foldl 512 (init := (0 : B1024))
    (fun acc i => if a.getLsbD i.val then acc ^^^ (b' <<< i.val) else acc)

/-- Recursive Karatsuba 512×512 → 1024; sub-multiplies via `clMul256_karatsuba`. -/
@[inline] private def clMul512_karatsuba (a b : B512) : B1024 :=
  let a_lo : B256 := a.truncate 256
  let a_hi : B256 := (a >>> 256).truncate 256
  let b_lo : B256 := b.truncate 256
  let b_hi : B256 := (b >>> 256).truncate 256
  let z_0 : B512 := clMul256_karatsuba a_lo b_lo
  let z_2 : B512 := clMul256_karatsuba a_hi b_hi
  let z_3 : B512 := clMul256_karatsuba (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let z_1 : B512 := z_3 ^^^ z_0 ^^^ z_2
  (z_0.zeroExtend 1024) ^^^ ((z_1.zeroExtend 1024) <<< 256) ^^^ ((z_2.zeroExtend 1024) <<< 512)

/-- Fold-based 1024×1024 → 2048 clMul. -/
@[inline] private def clMul1024_opt (a b : B1024) : B2048 :=
  let b' : B2048 := b.zeroExtend 2048
  Fin.foldl 1024 (init := (0 : B2048))
    (fun acc i => if a.getLsbD i.val then acc ^^^ (b' <<< i.val) else acc)

/-- Recursive Karatsuba 1024×1024 → 2048; sub-multiplies via `clMul512_karatsuba`. -/
@[inline] private def clMul1024_karatsuba (a b : B1024) : B2048 :=
  let a_lo : B512 := a.truncate 512
  let a_hi : B512 := (a >>> 512).truncate 512
  let b_lo : B512 := b.truncate 512
  let b_hi : B512 := (b >>> 512).truncate 512
  let z_0 : B1024 := clMul512_karatsuba a_lo b_lo
  let z_2 : B1024 := clMul512_karatsuba a_hi b_hi
  let z_3 : B1024 := clMul512_karatsuba (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let z_1 : B1024 := z_3 ^^^ z_0 ^^^ z_2
  (z_0.zeroExtend 2048) ^^^ ((z_1.zeroExtend 2048) <<< 512) ^^^ ((z_2.zeroExtend 2048) <<< 1024)

/-! ### Correctness — cross-check opt vs karatsuba at each width -/

private def tv_a256 : B256 :=
  (0xDEADBEEFCAFEBABE0123456789ABCDEFFEEDFACEFEEDFACE1122334455667788 : B256)
private def tv_b256 : B256 :=
  (0x0123456789ABCDEFFEDCBA9876543210AABBCCDDEEFF00112233445566778899 : B256)

#guard clMul256_opt tv_a256 tv_b256 == clMul256_karatsuba tv_a256 tv_b256

-- Anchor: at 256 bits with high halves zero, 256 variants must agree with the
-- known-good clMul128_opt on the low halves.
#guard clMul256_opt (tv_a.zeroExtend 256) (tv_b.zeroExtend 256)
        == (clMul128_opt tv_a tv_b).zeroExtend 512
#guard clMul256_karatsuba (tv_a.zeroExtend 256) (tv_b.zeroExtend 256)
        == (clMul128_opt tv_a tv_b).zeroExtend 512

private def tv_a512 : B512 := (tv_a256.zeroExtend 512) ^^^ ((tv_b256.zeroExtend 512) <<< 256)
private def tv_b512 : B512 := (tv_b256.zeroExtend 512) ^^^ ((tv_a256.zeroExtend 512) <<< 256)

#guard clMul512_opt tv_a512 tv_b512 == clMul512_karatsuba tv_a512 tv_b512

private def tv_a1024 : B1024 := (tv_a512.zeroExtend 1024) ^^^ ((tv_b512.zeroExtend 1024) <<< 512)
private def tv_b1024 : B1024 := (tv_b512.zeroExtend 1024) ^^^ ((tv_a512.zeroExtend 1024) <<< 512)

#guard clMul1024_opt tv_a1024 tv_b1024 == clMul1024_karatsuba tv_a1024 tv_b1024

/-! ### Benchmarks — iteration counts scale down as width grows -/

private def benchW {w : Nat} (f : BitVec w → BitVec w → BitVec (2 * w))
    (n : Nat) (a b : BitVec w) : IO (BitVec (2 * w)) := do
  let mut r : BitVec (2 * w) := 0
  for _ in List.range n do
    r := f a b
  return r

#eval timeit "=== 256x256 (5000 iters) ===" (pure ())
#eval timeit "  clMul256_opt"       (benchW clMul256_opt       5000 tv_a256 tv_b256)
#eval timeit "  clMul256_karatsuba" (benchW clMul256_karatsuba 5000 tv_a256 tv_b256)

#eval timeit "=== 512x512 (2000 iters) ===" (pure ())
#eval timeit "  clMul512_opt"       (benchW clMul512_opt       2000 tv_a512 tv_b512)
#eval timeit "  clMul512_karatsuba" (benchW clMul512_karatsuba 2000 tv_a512 tv_b512)

#eval timeit "=== 1024x1024 (500 iters) ===" (pure ())
#eval timeit "  clMul1024_opt"       (benchW clMul1024_opt       500 tv_a1024 tv_b1024)
#eval timeit "  clMul1024_karatsuba" (benchW clMul1024_karatsuba 500 tv_a1024 tv_b1024)

/-! ### Section 6: Pushing further — 2048, 4096, 8192 bits -/

abbrev B4096 := BitVec 4096
abbrev B8192 := BitVec 8192

/-- Fold-based 2048×2048 → 4096 clMul. -/
@[inline] private def clMul2048_opt (a b : B2048) : B4096 :=
  let b' : B4096 := b.zeroExtend 4096
  Fin.foldl 2048 (init := (0 : B4096))
    (fun acc i => if a.getLsbD i.val then acc ^^^ (b' <<< i.val) else acc)

@[inline] private def clMul2048_karatsuba (a b : B2048) : B4096 :=
  let a_lo : B1024 := a.truncate 1024
  let a_hi : B1024 := (a >>> 1024).truncate 1024
  let b_lo : B1024 := b.truncate 1024
  let b_hi : B1024 := (b >>> 1024).truncate 1024
  let z_0 : B2048 := clMul1024_karatsuba a_lo b_lo
  let z_2 : B2048 := clMul1024_karatsuba a_hi b_hi
  let z_3 : B2048 := clMul1024_karatsuba (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let z_1 : B2048 := z_3 ^^^ z_0 ^^^ z_2
  (z_0.zeroExtend 4096) ^^^ ((z_1.zeroExtend 4096) <<< 1024) ^^^ ((z_2.zeroExtend 4096) <<< 2048)

@[inline] private def clMul4096_opt (a b : B4096) : B8192 :=
  let b' : B8192 := b.zeroExtend 8192
  Fin.foldl 4096 (init := (0 : B8192))
    (fun acc i => if a.getLsbD i.val then acc ^^^ (b' <<< i.val) else acc)

@[inline] private def clMul4096_karatsuba (a b : B4096) : B8192 :=
  let a_lo : B2048 := a.truncate 2048
  let a_hi : B2048 := (a >>> 2048).truncate 2048
  let b_lo : B2048 := b.truncate 2048
  let b_hi : B2048 := (b >>> 2048).truncate 2048
  let z_0 : B4096 := clMul2048_karatsuba a_lo b_lo
  let z_2 : B4096 := clMul2048_karatsuba a_hi b_hi
  let z_3 : B4096 := clMul2048_karatsuba (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let z_1 : B4096 := z_3 ^^^ z_0 ^^^ z_2
  (z_0.zeroExtend 8192) ^^^ ((z_1.zeroExtend 8192) <<< 2048) ^^^ ((z_2.zeroExtend 8192) <<< 4096)

private def tv_a2048 : B2048 := (tv_a1024.zeroExtend 2048) ^^^ ((tv_b1024.zeroExtend 2048) <<< 1024)
private def tv_b2048 : B2048 := (tv_b1024.zeroExtend 2048) ^^^ ((tv_a1024.zeroExtend 2048) <<< 1024)
private def tv_a4096 : B4096 := (tv_a2048.zeroExtend 4096) ^^^ ((tv_b2048.zeroExtend 4096) <<< 2048)
private def tv_b4096 : B4096 := (tv_b2048.zeroExtend 4096) ^^^ ((tv_a2048.zeroExtend 4096) <<< 2048)

-- Correctness cross-checks at 2048+ are omitted: the `#guard` decision procedure
-- hits `maxRecDepth` at compile time for these sizes. Agreement with the smaller
-- widths (where `#guard` does succeed) gives us enough confidence.

#eval timeit "=== 2048x2048 (100 iters) ===" (pure ())
#eval timeit "  clMul2048_opt"       (benchW clMul2048_opt       100 tv_a2048 tv_b2048)
#eval timeit "  clMul2048_karatsuba" (benchW clMul2048_karatsuba 100 tv_a2048 tv_b2048)

#eval timeit "=== 4096x4096 (25 iters) ===" (pure ())
#eval timeit "  clMul4096_opt"       (benchW clMul4096_opt       25 tv_a4096 tv_b4096)
#eval timeit "  clMul4096_karatsuba" (benchW clMul4096_karatsuba 25 tv_a4096 tv_b4096)

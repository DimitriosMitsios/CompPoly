/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Multivariate.Rename

/-!
# Properties of algebra evaluation for `CMvPolynomial`

This file proves properties of the `aeval` function defined in `CMvPolynomial.lean`,
by transferring results from Mathlib's `MvPolynomial.aeval` through the
`fromCMvPolynomial` equivalence.

## Main results

* `aeval_equiv` — correspondence between `CMvPolynomial.aeval` and `MvPolynomial.aeval`
* `aeval_C` — evaluating a constant polynomial yields the algebra map
* `aeval_X` — evaluating a variable yields the assigned value

-/

namespace CPoly

open Std CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

omit [BEq R] [LawfulBEq R] in
/-- `CMvPolynomial.aeval` corresponds to `MvPolynomial.aeval` under `fromCMvPolynomial`. -/
lemma aeval_equiv {σ : Type} [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) :
    CMvPolynomial.aeval f p = MvPolynomial.aeval f (fromCMvPolynomial p) := by
  unfold CMvPolynomial.aeval MvPolynomial.aeval MvPolynomial.eval₂Hom
  simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  exact eval₂_equiv

/-- Evaluating a constant polynomial yields the algebra map of the constant. -/
@[simp]
lemma aeval_C {σ : Type} [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (c : R) :
    CMvPolynomial.aeval f (C (n := n) c) = algebraMap R σ c := by
  rw [aeval_equiv, fromCMvPolynomial_C, MvPolynomial.aeval_C]

/-- Evaluating a variable polynomial yields the assigned value. -/
@[simp]
lemma aeval_X {σ : Type} [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (i : Fin n) :
    CMvPolynomial.aeval f (X (R := R) i) = f i := by
  rw [aeval_equiv, fromCMvPolynomial_X, MvPolynomial.aeval_X]

end CPoly

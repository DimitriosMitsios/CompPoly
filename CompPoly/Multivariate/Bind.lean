/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Multivariate.Aeval
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Properties of variable substitution (`bind₁`) for `CMvPolynomial`

This file proves properties of the `bind₁` function defined in `CMvPolynomial.lean`,
by transferring results from Mathlib's `MvPolynomial.bind₁` through the
`fromCMvPolynomial` equivalence.

## Main results

* `fromCMvPolynomial_bind₁` — correspondence between `CMvPolynomial.bind₁` and
  `MvPolynomial.bind₁`
* `bind₁_C_right`, `bind₁_X_right` — behavior on constants and variables
* `bind₁_bind₁` — associativity of substitution

-/

namespace CPoly

open Std CMvPolynomial

variable {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-! ### Helper lemmas -/

/-- `fromCMvPolynomial` preserves exponentiation. -/
lemma fromCMvPolynomial_pow {k : ℕ} (p : CMvPolynomial k R) (e : ℕ) :
    fromCMvPolynomial (p ^ e) = (fromCMvPolynomial p) ^ e := by
  induction e with
  | zero => simp [map_one]
  | succ e ih => simp [pow_succ, map_mul, ih]

private lemma list_foldl_mul_eq_mul_prod [Monoid β]
    (l : List α) (f : α → β) (init : β) :
    l.foldl (fun acc x => acc * f x) init = init * (l.map f).prod := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih => simp [ih, mul_assoc]

private lemma fromCMvPolynomial_list_prod {k : ℕ}
    (l : List (CMvPolynomial k R)) :
    fromCMvPolynomial l.prod = (l.map fromCMvPolynomial).prod := by
  induction l with
  | nil => simp [map_one]
  | cons h t ih => simp [List.prod_cons, map_mul, ih]

/-- The inner product fold in `bind₁` corresponds to a `Finsupp.prod` under
`fromCMvPolynomial`. -/
lemma fromCMvPolynomial_inner_prod
    (f : Fin n → CMvPolynomial m R) (mono : CMvMonomial n) :
    fromCMvPolynomial ((List.finRange n).foldl
      (fun prod i => prod * (f i) ^ (mono.get i)) 1) =
    Finsupp.prod (CMvMonomial.toFinsupp mono)
      (fun i k => fromCMvPolynomial (f i) ^ k) := by
  rw [list_foldl_mul_eq_mul_prod, one_mul, fromCMvPolynomial_list_prod]
  simp only [List.map_map, Function.comp_def, fromCMvPolynomial_pow]
  rw [← List.ofFn_eq_map, List.prod_ofFn]
  unfold Finsupp.prod
  symm
  apply Finset.prod_subset
  · intro x hx; exact Finset.mem_univ x
  · intro x _ hx
    rw [Finsupp.notMem_support_iff] at hx
    simp [toFinsupp_apply, hx]

/-! ### Main correspondence lemma -/

/-- `CMvPolynomial.bind₁` agrees with `MvPolynomial.bind₁` under the
`fromCMvPolynomial` equivalence. -/
lemma fromCMvPolynomial_bind₁ (f : Fin n → CMvPolynomial m R)
    (p : CMvPolynomial n R) :
    fromCMvPolynomial (CMvPolynomial.bind₁ f p) =
    MvPolynomial.bind₁ (fun i => fromCMvPolynomial (f i))
      (fromCMvPolynomial p) := by
  sorry

/-! ### Transfer properties -/

/-- Substitution on a constant polynomial returns the constant. -/
@[simp]
lemma bind₁_C_right (f : Fin n → CMvPolynomial m R) (c : R) :
    CMvPolynomial.bind₁ f (C c) = C (n := m) c := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_bind₁, fromCMvPolynomial_C, fromCMvPolynomial_C]
  exact MvPolynomial.bind₁_C_right _ c

/-- Substitution on a variable returns the assigned polynomial. -/
@[simp]
lemma bind₁_X_right (f : Fin n → CMvPolynomial m R) (i : Fin n) :
    CMvPolynomial.bind₁ f (X (R := R) i) = f i := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_bind₁, fromCMvPolynomial_X]
  exact MvPolynomial.bind₁_X_right _ i

/-- Substitution is associative: substituting then substituting again
equals a single substitution with composed maps. -/
lemma bind₁_bind₁ {k : ℕ} (f : Fin n → CMvPolynomial m R)
    (g : Fin m → CMvPolynomial k R) (p : CMvPolynomial n R) :
    CMvPolynomial.bind₁ g (CMvPolynomial.bind₁ f p) =
    CMvPolynomial.bind₁ (fun i => CMvPolynomial.bind₁ g (f i)) p := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_bind₁, fromCMvPolynomial_bind₁, fromCMvPolynomial_bind₁]
  simp only [fromCMvPolynomial_bind₁]
  exact MvPolynomial.bind₁_bind₁ _ _ _

end CPoly

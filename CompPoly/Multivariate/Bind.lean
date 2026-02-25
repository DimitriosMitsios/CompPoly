/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Multivariate.Aeval
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Variable substitution (`bind₁`) for `CMvPolynomial`

This file defines `bind₁` and proves its properties by transferring results
from Mathlib's `MvPolynomial.bind₁` through the `fromCMvPolynomial` equivalence.

## Main definitions

* `CMvPolynomial.bind₁` — substitution of polynomials for variables, defined via `aeval`.

## Main results

* `fromCMvPolynomial_bind₁` — correspondence between `CMvPolynomial.bind₁` and
  `MvPolynomial.bind₁`
* `bind₁_C_right`, `bind₁_X_right` — behavior on constants and variables
* `bind₁_bind₁` — associativity of substitution

-/

namespace CPoly

open Std CMvPolynomial

variable {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Substitution: substitutes polynomials for variables.

  Given `f : Fin n → CMvPolynomial m R`, substitutes `f i` for variable `X i`.
  Defined as `aeval` using the `Algebra R (CMvPolynomial m R)` instance.
-/
def CMvPolynomial.bind₁ {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  aeval f p

/-- `polyRingEquiv` as an `AlgHom` from `CMvPolynomial` to `MvPolynomial`. -/
private noncomputable def fromCMvPolynomialAlgHom :
    CMvPolynomial m R →ₐ[R] MvPolynomial (Fin m) R where
  toFun := fromCMvPolynomial
  map_one' := map_one
  map_mul' := map_mul
  map_zero' := map_zero
  map_add' := map_add
  commutes' := fun c => by
    show fromCMvPolynomial (algebraMap R (CMvPolynomial m R) c) = algebraMap R _ c
    rw [MvPolynomial.algebraMap_eq]
    show fromCMvPolynomial ((CRingHom m R) c) = MvPolynomial.C c
    simp [CRingHom, fromCMvPolynomial_C]

/-- `CMvPolynomial.bind₁` agrees with `MvPolynomial.bind₁` under the
`fromCMvPolynomial` equivalence. -/
lemma fromCMvPolynomial_bind₁ (f : Fin n → CMvPolynomial m R)
    (p : CMvPolynomial n R) :
    fromCMvPolynomial (CMvPolynomial.bind₁ f p) =
    MvPolynomial.bind₁ (fun i => fromCMvPolynomial (f i))
      (fromCMvPolynomial p) := by
  -- Both sides are algebra homs in p. Show they agree on generators X i and constants C c.
  -- Both sides are algebra hom compositions that agree on generators.
  -- LHS alg hom: fromCMvPolynomialAlgHom ∘ₐ (CMvPolynomial.aeval f viewed as AlgHom)
  -- RHS alg hom: MvPolynomial.bind₁ (fromCMvPolynomial ∘ f) = MvPolynomial.aeval (fromCMvPolynomial ∘ f)
  -- Use MvPolynomial.algHom_ext: two AlgHoms from MvPolynomial agree iff they agree on X i.
  have : fromCMvPolynomialAlgHom.comp (MvPolynomial.aeval f) =
      MvPolynomial.aeval (fun i => fromCMvPolynomial (f i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [fromCMvPolynomialAlgHom, MvPolynomial.aeval_X]
  unfold CMvPolynomial.bind₁ MvPolynomial.bind₁
  -- aeval_equiv: CMvPolynomial.aeval f p = MvPolynomial.aeval f (fromCMvPolynomial p)
  -- Here σ = CMvPolynomial m R, so both sides are CMvPolynomial m R
  -- Applying fromCMvPolynomial to both sides of aeval_equiv:
  conv_lhs => rw [aeval_equiv]
  -- Now LHS = fromCMvPolynomial (MvPolynomial.aeval f (fromCMvPolynomial p))
  -- = (fromCMvPolynomialAlgHom.comp (MvPolynomial.aeval f)) (fromCMvPolynomial p)
  show (fromCMvPolynomialAlgHom.comp (MvPolynomial.aeval f)) (fromCMvPolynomial p) = _
  rw [this]

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

/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitrios Mitsios
-/

import CompPoly.Bivariate.ToPoly
import CompPoly.Multivariate.FinSuccEquiv

/-!
# Equivalence between `CBivariate R` and `CMvPolynomial 2 R`

Ring equivalence `CBivariate R ≃+* CMvPolynomial 2 R`, composed from:

1. `CBivariate.ringEquiv : CBivariate R ≃+* R[X][Y]`
2. `Polynomial.mapEquiv univarEquiv.symm : R[X][Y] ≃+* Polynomial (CMvPolynomial 1 R)`
3. `CMvPolynomial.finSuccEquiv.symm : Polynomial (CMvPolynomial 1 R) ≃+* CMvPolynomial 2 R`

The equivalence is `noncomputable` since it passes through Mathlib's `MvPolynomial`.

## Main definitions

* `CBivariate.bivariateEquiv` — the composed ring equivalence
* `CBivariate.univarEquiv` — auxiliary equivalence `CMvPolynomial 1 R ≃+* Polynomial R`

## Main results

* `bivariateEquiv_symm_apply_apply` — left-inverse round-trip
* `bivariateEquiv_apply_symm_apply` — right-inverse round-trip
* `bivariateEquiv_zero`, `bivariateEquiv_one` — preservation of constants
* `bivariateEquiv_add`, `bivariateEquiv_mul` — preservation of ring operations
-/

open Polynomial CPoly

namespace CompPoly

namespace CBivariate

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]

/-- Auxiliary equivalence: `CMvPolynomial 1 R ≃+* Polynomial R`, composing
`finSuccEquiv` (splitting off the single variable) with `mapEquiv isEmptyRingEquiv`
(collapsing the trivial `CMvPolynomial 0 R` coefficient ring to `R`). -/
noncomputable def univarEquiv : CMvPolynomial 1 R ≃+* Polynomial R :=
  (CMvPolynomial.finSuccEquiv (n := 0) (R := R)).trans
    (Polynomial.mapEquiv CMvPolynomial.isEmptyRingEquiv)

/-- Ring equivalence between `CBivariate R` and `CMvPolynomial 2 R`.

Composed as:
`CBivariate R ≃+* R[X][Y] ≃+* Polynomial (CMvPolynomial 1 R) ≃+* CMvPolynomial 2 R`. -/
noncomputable def bivariateEquiv : CBivariate R ≃+* CMvPolynomial 2 R :=
  ringEquiv.trans <|
    (Polynomial.mapEquiv univarEquiv.symm).trans <|
      (CMvPolynomial.finSuccEquiv (n := 1) (R := R)).symm

@[simp]
theorem bivariateEquiv_symm_apply_apply (p : CBivariate R) :
    bivariateEquiv.symm (bivariateEquiv p) = p :=
  bivariateEquiv.symm_apply_apply p

@[simp]
theorem bivariateEquiv_apply_symm_apply (p : CMvPolynomial 2 R) :
    bivariateEquiv (bivariateEquiv.symm p) = p :=
  bivariateEquiv.apply_symm_apply p

theorem bivariateEquiv_add (p q : CBivariate R) :
    bivariateEquiv (p + q) = bivariateEquiv p + bivariateEquiv q :=
  bivariateEquiv.map_add p q

theorem bivariateEquiv_mul (p q : CBivariate R) :
    bivariateEquiv (p * q) = bivariateEquiv p * bivariateEquiv q :=
  bivariateEquiv.map_mul p q

@[simp]
theorem bivariateEquiv_zero : bivariateEquiv (0 : CBivariate R) = 0 :=
  map_zero bivariateEquiv

@[simp]
theorem bivariateEquiv_one : bivariateEquiv (1 : CBivariate R) = 1 :=
  map_one bivariateEquiv

theorem bivariateEquiv_injective :
    Function.Injective (bivariateEquiv (R := R)) :=
  bivariateEquiv.injective

theorem bivariateEquiv_surjective :
    Function.Surjective (bivariateEquiv (R := R)) :=
  bivariateEquiv.surjective

/-- Ring homomorphism from `CBivariate R` to `CMvPolynomial 2 R`. -/
noncomputable def bivariateEquivHom : CBivariate R →+* CMvPolynomial 2 R :=
  bivariateEquiv.toRingHom

/-- Ring homomorphism from `CMvPolynomial 2 R` to `CBivariate R`. -/
noncomputable def bivariateEquivSymmHom : CMvPolynomial 2 R →+* CBivariate R :=
  bivariateEquiv.symm.toRingHom

end CBivariate

end CompPoly

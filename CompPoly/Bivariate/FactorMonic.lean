/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Factor
import CompPoly.Univariate.DivisionCorrectness

/-!
# Bridge: synthetic linear division vs. general monic division (WORK IN PROGRESS)

This file states — but does **not** yet prove — that the bespoke synthetic
division `divByLinearY Q f` (Horner) coincides with general monic Euclidean
division of `Q` by the linear factor `Y - f`, using the now-`CommRing`-general
`CPolynomial.divByMonic` / `CPolynomial.modByMonic` at the coefficient ring
`CPolynomial R` (recall `CBivariate R = CPolynomial (CPolynomial R)`).

The two sorried theorems below are the handoff target. Once proved, the root
API (`evalYPoly`, `isLinearYFactor`, `divByLinearY_exact`, the remainder/
evaluation identity) can be re-expressed on top of `divByMonic`, and the
question of whether to retire `divByLinearY` reduces to a pure benchmark.

This module is intentionally **not** registered in `CompPoly.lean` (it contains
`sorry`); build it directly with
`lake build CompPoly.Bivariate.FactorMonic`.

## Why it is nontrivial

There are two *different* `toPoly` bridges in play, and the proof has to cross
between them:

* `CBivariate.toPoly : CBivariate R → R[X][Y]` — used by `divByLinearY_spec`
  (coefficients are genuine Mathlib `R[X]`).
* `CPolynomial.toPoly : CPolynomial (CPolynomial R) → (CPolynomial R)[Y]` — used
  by `divByMonic_toPoly_eq_divByMonic` (coefficients are the *computable*
  `CPolynomial R`).

They are related by mapping the coefficient ring through the ring isomorphism
`CPolynomial.ringEquiv : CPolynomial R ≃+* R[X]` coefficientwise; see
`CBivariate.toPoly_eq_map` and the pattern in `CBivariate.evalYPoly_toPoly`.

## Recommended proof strategy

Prefer the *uniqueness of monic division* route, staying at the
`CPolynomial.toPoly` level (avoids one of the two bridges):

1. `linearYDivisor_monic`: show `Y - f` is monic. Working at `CPolynomial.toPoly`
   (into `(CPolynomial R)[Y]`), its image is `Polynomial.X - Polynomial.C f`
   (coefficient `f : CPolynomial R`, *not* `f.toPoly`), monic of degree `1`
   (`Polynomial.monic_X_sub_C`). `CPolynomial.monic` ↔ `.toPoly.Monic` is
   `CPolynomial.monic_toPoly_iff`; combine with `CPolynomial.toPoly_sub`,
   `CPolynomial.X_toPoly`, `CPolynomial.C_toPoly`.
2. Establish the ring-level Euclidean identity in `CBivariate R`:
   `Q = linearYDivisor f * (divByLinearY Q f).1 + CPolynomial.C (divByLinearY Q f).2`.
   The cleanest source is the coefficient-level facts already proved in
   `Factor.lean` — `divByLinearY_quot_recurrence` and `divByLinearY_rem_formula`
   — fed through `CPolynomial.eq_iff_coeff`; alternatively recover it from
   `divByLinearY_spec` by injectivity of `CBivariate.toPoly`.
3. Apply `CPolynomial.toPoly` to that identity and use
   `Polynomial.div_modByMonic_unique` (the remainder `C (divByLinearY Q f).2`
   has `Y`-degree `0 < 1`, so `degree (C rem).toPoly < degree (Y - f).toPoly`)
   to identify the quotient with `Q.toPoly /ₘ (Y-f).toPoly` and the remainder
   with `Q.toPoly %ₘ (Y-f).toPoly`.
4. Rewrite those with `CPolynomial.divByMonic_toPoly_eq_divByMonic` /
   `CPolynomial.modByMonic_toPoly_eq_modByMonic`, then conclude the
   `CBivariate`-level equalities by `CPolynomial.eq_iff_coeff` +
   `CPolynomial.coeff_toPoly` (the same injectivity trick used in
   `CPolynomial.modByMonic_add_mul_divByMonic`).

## Useful lemmas

`CPolynomial.divByMonic_toPoly_eq_divByMonic`,
`CPolynomial.modByMonic_toPoly_eq_modByMonic`,
`CPolynomial.modByMonic_add_mul_divByMonic`, `CPolynomial.monic_toPoly_iff`,
`CPolynomial.eq_iff_coeff`, `CPolynomial.coeff_toPoly`,
`Polynomial.div_modByMonic_unique`, `Polynomial.monic_X_sub_C`,
`CPolynomial.toPoly_sub`, `CPolynomial.X_toPoly`, `CPolynomial.C_toPoly`,
`CBivariate.divByLinearY_spec`, `CBivariate.divByLinearY_rem_eq_eval`,
`CBivariate.divByLinearY_quot_recurrence`, `CBivariate.divByLinearY_rem_formula`,
`CBivariate.toPoly_eq_map`.

## Done = no `sorry`; the file builds; the two theorems hold.
-/

namespace CompPoly

namespace CBivariate

variable {R : Type*}

/-- The linear monic divisor `Y - f`, as a bivariate polynomial
(`CBivariate R = CPolynomial (CPolynomial R)`). -/
def linearYDivisor [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) : CBivariate R :=
  -- `CPolynomial.X` at this nested type is `Y`; it is defeq to `CBivariate.X`.
  (CPolynomial.X : CPolynomial (CPolynomial R)) - CPolynomial.C f

/-- TODO (aleph): the linear divisor `Y - f` is monic. -/
theorem linearYDivisor_monic [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CPolynomial R) :
    CPolynomial.monic (linearYDivisor f) = true := by
  sorry

theorem linearYDivisor_toPoly [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] (f : CPolynomial R) : CPolynomial.toPoly (linearYDivisor f) = Polynomial.X - Polynomial.C f := by
  simpa [linearYDivisor, CPolynomial.X_toPoly, CPolynomial.C_toPoly] using
    (CPolynomial.toPoly_sub (p := (CPolynomial.X : CPolynomial (CPolynomial R))) (q := CPolynomial.C f))

theorem divByLinearY_euclid_toPoly [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) : (CPolynomial.C (divByLinearY Q f).2).toPoly + CPolynomial.toPoly (linearYDivisor f) * CPolynomial.toPoly ((divByLinearY Q f).1) = CPolynomial.toPoly Q := by
  let e := (CPolynomial.ringEquiv (R := R)).toRingHom
  apply Polynomial.map_injective e (CPolynomial.ringEquiv (R := R)).injective
  rw [Polynomial.map_add, Polynomial.map_mul, CPolynomial.C_toPoly, linearYDivisor_toPoly (R := R) f]
  simp only [Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X]
  simpa [e, CBivariate.toPoly_eq_map, mul_comm, add_comm, add_left_comm, add_assoc] using
    (divByLinearY_spec Q f).symm

theorem linearYDivisor_monic_aux [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] (f : CPolynomial R) : CPolynomial.monic (linearYDivisor f) = true := by
  have hpoly := linearYDivisor_toPoly (R := R) f
  have hmonic : (CPolynomial.toPoly (linearYDivisor f)).Monic := by
    rw [hpoly]
    exact Polynomial.monic_X_sub_C f
  exact (CPolynomial.monic_toPoly_iff (linearYDivisor f)).2 hmonic

theorem divByLinearY_eq_divByMonic [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    CPolynomial.divByMonic Q (linearYDivisor f) = (divByLinearY Q f).1
      ∧ CPolynomial.modByMonic Q (linearYDivisor f)
          = CPolynomial.C (divByLinearY Q f).2 := by
  let g := linearYDivisor f
  let q := (divByLinearY Q f).1
  let r := (divByLinearY Q f).2
  have hg : CPolynomial.monic g := by
    simpa [g] using linearYDivisor_monic_aux (R := R) f
  have hg_toPoly : (CPolynomial.toPoly g).Monic :=
    (CPolynomial.monic_toPoly_iff g).1 hg
  have he : (CPolynomial.C r).toPoly + CPolynomial.toPoly g * CPolynomial.toPoly q = CPolynomial.toPoly Q := by
    simpa [g, q, r] using divByLinearY_euclid_toPoly (R := R) Q f
  have hdeg : ((CPolynomial.C r).toPoly).degree < (CPolynomial.toPoly g).degree := by
    rw [CPolynomial.C_toPoly, linearYDivisor_toPoly (R := R) f]
    by_cases hr : r = 0 <;> simp [hr, Polynomial.degree_X_sub_C]
  have huniq := Polynomial.div_modByMonic_unique
      (f := CPolynomial.toPoly Q) (g := CPolynomial.toPoly g)
      (q := CPolynomial.toPoly q) (r := (CPolynomial.C r).toPoly)
      hg_toPoly ⟨he, hdeg⟩
  have hdiv : CPolynomial.toPoly (CPolynomial.divByMonic Q g) = CPolynomial.toPoly q := by
    rw [CPolynomial.divByMonic_toPoly_eq_divByMonic Q g hg]
    exact huniq.1
  have hmod : CPolynomial.toPoly (CPolynomial.modByMonic Q g) = CPolynomial.toPoly (CPolynomial.C r) := by
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic Q g hg]
    exact huniq.2
  constructor
  · apply CPolynomial.eq_iff_coeff.2
    intro i
    have hi := congrArg (fun p : Polynomial (CPolynomial R) => p.coeff i) hdiv
    simpa only [CPolynomial.coeff_toPoly, g, q] using hi
  · apply CPolynomial.eq_iff_coeff.2
    intro i
    have hi := congrArg (fun p : Polynomial (CPolynomial R) => p.coeff i) hmod
    simpa only [CPolynomial.coeff_toPoly, g, r] using hi


end CBivariate

end CompPoly

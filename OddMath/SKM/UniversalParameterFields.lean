/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.UniversalCoefficientReduced
import OddMath.SKM.UniversalCoefficientRationalization

/-!
# Prime fraction fields of universal parameters

The separating-field family in `GroundRingDescent.md` §4, supporting the
proposed deduction from Brundan–Ellis, arXiv:1701.04133v2, Theorem 8.1
and the §8 conjecture. Rationalization retains the unsaturated normalization
group and all coefficient slots. The prime fraction fields jointly detect
parameters, though no individual map need be injective.
-/

noncomputable section
namespace OddMath.SKM.UniversalParameterFields

open UniversalPolynomialParameters UniversalCoefficientRationalization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- Rational parameters on exactly the allowed coefficient slots. -/
abbrev RationalParameters :=
  MvPolynomial (Slot D) (RationalUnitRing D)

/-- Fraction field of a prime quotient of the rational parameters. -/
abbrev FieldAt (p : PrimeSpectrum (RationalParameters D)) :=
  primeFractionField (RationalParameters D) p

instance field (p : PrimeSpectrum (RationalParameters D)) : Field (FieldAt D p) :=
  inferInstance

instance charZero (p : PrimeSpectrum (RationalParameters D)) : CharZero (FieldAt D p) :=
  inferInstance

/-- The actual integral-parameter point of a rational prime fraction field. -/
def point (p : PrimeSpectrum (RationalParameters D)) :
    ParameterRing D →+* FieldAt D p :=
  (primeFractionMap (RationalParameters D) p).comp
    (rationalizePolynomial D (Slot D))

/-- All prime fraction fields together reflect zero in the original ring. -/
theorem point_separate (a : ParameterRing D)
    (h : ∀ p, point D p a = 0) : a = 0 := by
  apply rationalizePolynomial_injective D (Slot D)
  have hq : rationalizePolynomial D (Slot D) a = 0 :=
    UniversalCoefficientReduced.rationalParameters_separate D _ h
  simpa using hq

/-- Every nonzero universal parameter survives in some characteristic-zero field. -/
theorem exists_point_ne_zero {a : ParameterRing D} (ha : a ≠ 0) :
    ∃ p : PrimeSpectrum (RationalParameters D), point D p a ≠ 0 := by
  by_contra hn
  apply ha
  apply point_separate D a
  intro p
  by_contra hp
  exact hn ⟨p, hp⟩

@[simp] theorem point_C (p : PrimeSpectrum (RationalParameters D))
    (a : UniversalCoefficientRing.UnitRing D) :
    point D p (MvPolynomial.C a) =
      primeFractionMap (RationalParameters D) p (MvPolynomial.C (rationalize D a)) := by
  simp [point]

@[simp] theorem point_X (p : PrimeSpectrum (RationalParameters D)) (s : Slot D) :
    point D p (MvPolynomial.X s) =
      primeFractionMap (RationalParameters D) p (MvPolynomial.X s) := by
  simp [point]

@[simp] theorem point_t (p : PrimeSpectrum (RationalParameters D)) (i j : I) :
    point D p (MvPolynomial.C (UniversalCoefficientRing.t D i j :
      UniversalCoefficientRing.UnitRing D)) =
      primeFractionMap (RationalParameters D) p
        (MvPolynomial.C (AddMonoidAlgebra.single (NormalizationParameterGroup.t D i j) 1)) := by
  simp

@[simp] theorem point_c (p : PrimeSpectrum (RationalParameters D)) (μ : X) (i : I) :
    point D p (MvPolynomial.C (UniversalCoefficientRing.c D μ i :
      UniversalCoefficientRing.UnitRing D)) =
      primeFractionMap (RationalParameters D) p
        (MvPolynomial.C (AddMonoidAlgebra.single (NormalizationParameterGroup.c D μ i) 1)) := by
  simp

/-- An allowed coefficient maps to its exact slot variable. -/
theorem point_coefficient_of_allowed (p : PrimeSpectrum (RationalParameters D))
    (a : RawSlot I) (h : Allowed D a) :
    point D p (coefficient D a) =
      primeFractionMap (RationalParameters D) p (MvPolynomial.X (slot D a h)) := by
  rw [coefficient_of_allowed D a h, point_X]

/-- A forbidden coefficient remains zero at every field point. -/
theorem point_coefficient_of_not_allowed (p : PrimeSpectrum (RationalParameters D))
    (a : RawSlot I) (h : ¬ Allowed D a) : point D p (coefficient D a) = 0 := by
  rw [coefficient_of_not_allowed D a h, map_zero]

/-- The scalar system at a point; the datum and weight group are unchanged. -/
def scalars (p : PrimeSpectrum (RationalParameters D)) : Scalars D (FieldAt D p) where
  t i j := Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.scalars D).t i j)
  t_self i := by simp [UniversalPolynomialParameters.scalars]
  t_symm_of_d_eq_zero i j h := by
    rw [(UniversalPolynomialParameters.scalars D).t_symm_of_d_eq_zero i j h]
  s i j m n := point D p ((UniversalPolynomialParameters.scalars D).s i j m n)
  s_symm i j m n := by rw [(UniversalPolynomialParameters.scalars D).s_symm]
  s_eq_zero i j m n h := by
    rw [(UniversalPolynomialParameters.scalars D).s_eq_zero i j m n h, map_zero]
  two_isUnit _ := isUnit_iff_ne_zero.mpr (by norm_num)

/-- Exact inherited homogeneity of every characteristic-zero point. -/
theorem homogeneous (p : PrimeSpectrum (RationalParameters D)) :
    (scalars D p).Homogeneous := by
  intro i j m n hm hm' hn hn' h
  apply UniversalPolynomialParameters.homogeneous D i j m n hm hm' hn hn'
  intro hz
  exact h (by simp [scalars, hz])

/-- Normalization units at every original weight, with no chosen sign of torsion. -/
def normalizations (p : PrimeSpectrum (RationalParameters D)) : CScalars (scalars D p) where
  c μ i := Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.normalizations D).c μ i)
  shift μ i j := by
    change Units.map (point D p).toMonoidHom
        ((UniversalPolynomialParameters.normalizations D).c (μ + D.α j) i) =
      Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.scalars D).t i j) *
        Units.map (point D p).toMonoidHom
          ((UniversalPolynomialParameters.normalizations D).c μ i)
    rw [(UniversalPolynomialParameters.normalizations D).shift μ i j]
    exact map_mul _ _ _

@[simp] theorem scalars_t (p : PrimeSpectrum (RationalParameters D)) (i j : I) :
    (scalars D p).t i j =
      Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.scalars D).t i j) := rfl

@[simp] theorem scalars_s (p : PrimeSpectrum (RationalParameters D))
    (i j : I) (m n : ℕ) :
    (scalars D p).s i j m n = point D p (coefficient D ⟨i, j, m, n⟩) := rfl

@[simp] theorem normalizations_c (p : PrimeSpectrum (RationalParameters D)) (μ : X) (i : I) :
    (normalizations D p).c μ i =
      Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.normalizations D).c μ i) := rfl

end OddMath.SKM.UniversalParameterFields

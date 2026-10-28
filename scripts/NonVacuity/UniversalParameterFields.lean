import OddMath.SKM.UniversalParameterFields

/-! GroundRingDescent §4 on the exact parameter ring: every nonzero slot
coefficient is detected by some prime field, with no selected prime.
The same family applies even to an empty colour type. -/

noncomputable section
namespace NonVacuity.UniversalParameterFields
open OddMath.SKM OddMath.SKM.UniversalPolynomialParameters
open OddMath.SKM.UniversalParameterFields

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

private theorem unitRing_nontrivial : Nontrivial (UniversalCoefficientRing.UnitRing D) := by
  have hbase : (1 : UniversalCoefficientRing.HalfIntegers) ≠ 0 := by
    intro h
    have hq := congrArg UniversalCoefficientRationalization.coefficientMap h
    norm_num at hq
  have hring : (1 : UniversalCoefficientRing.UnitRing D) ≠ 0 := by
    intro h
    apply hbase
    have hs : AddMonoidAlgebra.single (0 : NormalizationParameterGroup.Group D)
        (1 : UniversalCoefficientRing.HalfIntegers) =
        AddMonoidAlgebra.single 0 0 := by
      simpa [← AddMonoidAlgebra.one_def] using h
    exact AddMonoidAlgebra.single_right_injective hs
  exact nontrivial_of_ne 1 0 hring

/-- An actual allowed coefficient variable cannot disappear at every field point. -/
example (a : RawSlot I) (h : Allowed D a) :
    ∃ p : PrimeSpectrum (RationalParameters D),
      point D p (coefficient D a) ≠ 0 := by
  apply exists_point_ne_zero D
  rw [coefficient_of_allowed D a h]
  have : Nontrivial (UniversalCoefficientRing.UnitRing D) := unitRing_nontrivial D
  exact MvPolynomial.X_ne_zero (slot D a h)

example (a : RawSlot I) (h : Allowed D a) :
    ∃ p : PrimeSpectrum (RationalParameters D),
      primeFractionMap (RationalParameters D) p (MvPolynomial.X (slot D a h)) ≠ 0 := by
  obtain ⟨p, hp⟩ := (show ∃ p : PrimeSpectrum (RationalParameters D),
    point D p (coefficient D a) ≠ 0 from by
      apply exists_point_ne_zero D
      rw [coefficient_of_allowed D a h]
      have : Nontrivial (UniversalCoefficientRing.UnitRing D) := unitRing_nontrivial D
      exact MvPolynomial.X_ne_zero (slot D a h))
  exact ⟨p, by simpa [point_coefficient_of_allowed D p a h] using hp⟩

example (D : Datum Empty ℤ) (a : ParameterRing D)
    (h : ∀ p : PrimeSpectrum (RationalParameters D), point D p a = 0) : a = 0 :=
  point_separate D a h

example (p : PrimeSpectrum (RationalParameters D)) (i j : I) (μ : X) :
    Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.scalars D).t i j) =
      (UniversalParameterFields.scalars D p).t i j ∧
    Units.map (point D p).toMonoidHom ((UniversalPolynomialParameters.normalizations D).c μ i) =
      (UniversalParameterFields.normalizations D p).c μ i := ⟨rfl, rfl⟩

example (p : PrimeSpectrum (RationalParameters D)) :
    (UniversalParameterFields.scalars D p).Homogeneous := homogeneous D p

#print axioms OddMath.SKM.UniversalParameterFields.point
#print axioms OddMath.SKM.UniversalParameterFields.point_separate
#print axioms OddMath.SKM.UniversalParameterFields.exists_point_ne_zero
#print axioms OddMath.SKM.UniversalParameterFields.point_t
#print axioms OddMath.SKM.UniversalParameterFields.point_c
#print axioms OddMath.SKM.UniversalParameterFields.point_coefficient_of_allowed
#print axioms OddMath.SKM.UniversalParameterFields.point_coefficient_of_not_allowed
#print axioms OddMath.SKM.UniversalParameterFields.scalars
#print axioms OddMath.SKM.UniversalParameterFields.homogeneous
#print axioms OddMath.SKM.UniversalParameterFields.normalizations

end NonVacuity.UniversalParameterFields

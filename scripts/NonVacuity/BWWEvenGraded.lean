import OddMath.SKM.BWWEvenGraded
import NonVacuity.BWWEvenDictionary
import NonVacuity.BWWGradedParameters

/-! # The graded even dictionary

With `ℚ` concentrated in degree `0` and symmetrizer `(1, 1)`, the polynomials of
`u³ + v³ + 1` are not graded homogeneous: the constant term would need degree `6`. The
dictionary transports this from `BWWScalars.GradedHomogeneous`.
-/

noncomputable section
namespace NonVacuity.BWWEvenGraded
open OddMath OddMath.SKM NonVacuity.BWWScalars NonVacuity.BWWGradedParameters
  NonVacuity.BWWEvenDictionary

instance : SetLike.GradedOne grading := ⟨by simp [grading]⟩

example : ¬polys.GradedHomogeneous symmetrizer grading := by
  rw [← BWWPolynomials.gradedHomogeneous_toBWWScalars_iff _ _ _ even]
  rintro ⟨-, h⟩
  obtain ⟨n, hn, hmem⟩ := h true false 0 0 (by decide) (by rw [d_ne (by decide)]; norm_num)
    (by rw [d_ne (by decide)]; norm_num)
    (by rw [BWWPolynomials.toBWWScalars_c, coeff_constant]; norm_num)
  simp only [coefficientDegree, symmetrizer, d_ne (show true ≠ false by decide)] at hn
  have hn6 : n = 6 := by omega
  subst hn6
  rw [BWWPolynomials.toBWWScalars_c, coeff_constant] at hmem
  simp [grading] at hmem

end NonVacuity.BWWEvenGraded

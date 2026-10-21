import OddMath
import OddMath.SKM.CliffordK0Examples

noncomputable section

open CategoryTheory StringDiagrams OddMath.SKM.CliffordK0

example : c ℚ * c ℚ = 1 := c_mul_c ℚ
example : c ℚ ≠ 0 := c_ne_zero ℚ
example : (1 : Algebra ℚ) ≠ c ℚ := one_ne_c ℚ

example : K₀.mk (regular ℚ 1) = K₀.mk (regular ℚ 0) := by
  simpa using regular_parity_class ℚ 0

example : K₀.piInvolution ℚ (Projectives ℚ) =
    AddMonoidHom.id (K₀ (Projectives ℚ)) := piInvolution_eq_id ℚ

example : Nonempty (Projectives ℚ ≌ SKarAlg.FGProj (parity ℚ)) :=
  ⟨projectiveEquivalence ℚ⟩

example : Module (LaurentPolynomial Zπ) (K₀ (GradedProjectives ℚ)) :=
  laurentModule ℚ

example : K₀.mk (gradedRegular ℚ) ≠ 0 := gradedRegular_class_ne_zero ℚ

example (x : K₀ (GradedProjectives ℚ)) :
    letI := K₀.moduleLaurent ℚ (GradedProjectives ℚ)
    LaurentPolynomial.C Zπ.π • x = x := C_pi_smul ℚ x

example :
    letI := K₀.moduleLaurent ℚ (GradedProjectives ℚ)
    ¬ Module.Free (LaurentPolynomial Zπ) (K₀ (GradedProjectives ℚ)) :=
  gradedK0_not_free ℚ

#print axioms OddMath.SKM.CliffordK0.laurentian
#print axioms OddMath.SKM.CliffordK0.gradedRegular_class_ne_zero
#print axioms OddMath.SKM.CliffordK0.gradedProjectiveParityNatIso
#print axioms OddMath.SKM.CliffordK0.graded_piInvolution_eq_id
#print axioms OddMath.SKM.CliffordK0.C_pi_smul
#print axioms OddMath.SKM.CliffordK0.gradedK0_not_free
#print axioms OddMath.SKM.CliffordK0.c_mul_c
#print axioms OddMath.SKM.CliffordK0.projectiveK0Equiv
#print axioms OddMath.SKM.CliffordK0.piInvolution_eq_id
#print axioms OddMath.SKM.CliffordK0.projective_regular_parity_class

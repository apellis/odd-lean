import OddMath.SKM.CliffordK0

/-!
# The rational Clifford counterexample to Laurent freeness

Concrete consumers of the split Grothendieck group and Laurent action for the
Clifford algebra concentrated in integer degree zero.
-/

noncomputable section

namespace OddMath.SKM.CliffordK0.Examples

open CategoryTheory StringDiagrams

example : (∀ n : ℤ, FiniteDimensional ℚ (degree ℚ n)) ∧
    ∀ n : ℤ, n < 0 → degree ℚ n = ⊥ := laurentian ℚ

example : K₀.mk (gradedRegular ℚ) ≠ 0 := gradedRegular_class_ne_zero ℚ

example : K₀.piInvolution ℚ (GradedProjectives ℚ) =
    AddMonoidHom.id (K₀ (GradedProjectives ℚ)) := graded_piInvolution_eq_id ℚ

example (x : K₀ (GradedProjectives ℚ)) :
    letI := K₀.moduleLaurent ℚ (GradedProjectives ℚ)
    LaurentPolynomial.C Zπ.π • x = x := C_pi_smul ℚ x

example :
    letI := K₀.moduleLaurent ℚ (GradedProjectives ℚ)
    ¬ Module.Free (LaurentPolynomial Zπ) (K₀ (GradedProjectives ℚ)) :=
  gradedK0_not_free ℚ

end OddMath.SKM.CliffordK0.Examples

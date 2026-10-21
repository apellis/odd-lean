import OddMath

noncomputable section
namespace NonVacuity.LaurentianK0
open CategoryTheory StringDiagrams OddMath.SKM
open LaurentianK0Examples

example (a b : B) :
    letI := K₀.moduleLaurentInt ℚ (GSKAR.mkObj ℚ B a ⟶ GSKAR.mkObj ℚ B b)
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKAR.mkObj ℚ B a ⟶ GSKAR.mkObj ℚ B b)) :=
  k0_free a b

example (a b : B) := basis a b

example : K₀.mk KrullSchmidtLaurentExamples.line ≠ 0 :=
  KrullSchmidtLaurentExamples.line_class_ne_zero

end NonVacuity.LaurentianK0

import OddMath.Diagrams.OddNilHecke.CyclotomicNorm
import OddMath.Diagrams.OddNilHecke.ExteriorDeformation

noncomputable section
open OddMath.OddNilHecke ExteriorDeformation

example : exterior dualParameter ≠ 0 ∧
    (1 + firstDot dualParameter * exterior dualParameter) *
      (1 - firstDot dualParameter * exterior dualParameter) = 1 := by
  refine ⟨dualNumber_model.1, ?_⟩
  have hx := (exterior_anticommutes dualParameter
    (TrivSqZeroExt.inr_mul_inr ℚ 1 1)).1
  have ha : exterior dualParameter * firstDot dualParameter =
      -(firstDot dualParameter * exterior dualParameter) :=
    eq_neg_of_add_eq_zero_left hx
  simpa using CyclotomicNorm.even_cutoff_multiple
    (firstDot dualParameter) (exterior dualParameter) 1 1
    dualNumber_model.2.1 ha (by simp) (by simp) (by simp)

#print axioms CyclotomicNorm.exterior_term_square
#print axioms CyclotomicNorm.conjugate_product
#print axioms CyclotomicNorm.even_cutoff_multiple
#print axioms CyclotomicNorm.even_cutoff_transport_neg
#print axioms CyclotomicNorm.even_cutoff_transport_pos
#print axioms CyclotomicNorm.translated_square
#print axioms CyclotomicNorm.even_cutoff_translation_fixed

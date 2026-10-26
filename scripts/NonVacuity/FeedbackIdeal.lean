import OddMath.SKM.RouquierFeedbackIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! A nonzero square-zero coefficient ideal over ℤ/4 controls a full
matrix feedback operator. In particular, the ideal condition is inhabited
without setting the off-diagonal block or the feedback to zero. -/
noncomputable section
open Matrix OddMath.SKM.RouquierSchur
namespace NonVacuity.FeedbackIdeal

private def evenIdeal : TwoSidedIdeal (ZMod 4) :=
  TwoSidedIdeal.mk' {x | x = 0 ∨ x = 2}
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem evenIdeal_mem (x : ZMod 4) : x ∈ evenIdeal ↔ x = 0 ∨ x = 2 := by
  simp only [evenIdeal, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]

private theorem evenIdeal_sq : ∀ x y : ZMod 4,
    x ∈ evenIdeal → y ∈ evenIdeal → x * y = 0 := by
  simp only [evenIdeal_mem]
  decide

private def level (n : ℕ) : TwoSidedIdeal (ZMod 4) :=
  if n = 0 then ⊤ else if n = 1 then evenIdeal else ⊥

private def filtration : FeedbackIdealFiltration (ZMod 4) where
  level := level
  zero_eq_top := rfl
  mul_mem := by
    intro a b x y hx hy
    by_cases ha : a = 0
    · subst a
      simpa using (level b).mul_mem_left x y hy
    by_cases hb : b = 0
    · subst b
      simpa using (level a).mul_mem_right x y hx
    have hab0 : a + b ≠ 0 := by omega
    have hab1 : a + b ≠ 1 := by omega
    simp only [level, ite_eq_right hab0, ite_eq_right hab1, TwoSidedIdeal.mem_bot] at ⊢
    by_cases ha1 : a = 1
    · subst a
      by_cases hb1 : b = 1
      · subst b
        exact evenIdeal_sq x y (by simpa [level] using hx) (by simpa [level] using hy)
      · have hy0 : y = 0 := by simpa [level, hb, hb1] using hy
        simp [hy0]
    · have hx0 : x = 0 := by simpa [level, ha, ha1] using hx
      simp [hx0]

private def B : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![1, 1; 0, 1]
private def C : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![2, 0; 2, 2]
private theorem C_mem (i j : Fin 2) : C i j ∈ filtration.level 1 := by
  change C i j ∈ evenIdeal
  rw [evenIdeal_mem]
  fin_cases i <;> fin_cases j <;> decide

example : C * B ≠ 0 := by decide
example : B * C ≠ C * B := by decide

example : IsNilpotent (C * B) := by
  exact filtration.matrix_isNilpotent (C * B)
    (filtration.matrix_mul_mem_right C B 1 C_mem) 2 rfl

example : IsUnit (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 4)) B C 1) := by
  exact filtration.isUnit_of_ideal_feedback 1 1 B C C_mem 2 rfl

#print axioms FeedbackIdealFiltration.matrix_pow_mem
#print axioms FeedbackIdealFiltration.matrix_isNilpotent
#print axioms FeedbackIdealFiltration.isUnit_of_feedback_filtration
#print axioms FeedbackIdealFiltration.isUnit_of_ideal_feedback
end NonVacuity.FeedbackIdeal

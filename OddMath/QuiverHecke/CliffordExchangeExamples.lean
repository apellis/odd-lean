/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordExchange
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic

/-! # Concrete consumers of KKT's distant Clifford sign -/

noncomputable section
namespace OddMath.QuiverHecke.CliffordExchange.Examples

/-- The four-variable sum-of-squares Clifford form over the rational field. -/
def form : QuadraticForm ℚ (Fin 4 → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ (fun _ : Fin 4 => (1 : ℚ))

/-- Its orthogonal unit generators. -/
def generator (i : Fin 4) : CliffordAlgebra form := CliffordAlgebra.ι form (Pi.single i 1)

theorem generator_square (i : Fin 4) : generator i * generator i = 1 := by
  simp [generator, CliffordAlgebra.ι_sq_scalar, form, Pi.single_apply]

theorem generator_anticommute (i j : Fin 4) (hij : i ≠ j) :
    generator i * generator j = -(generator j * generator i) := by
  rw [eq_neg_iff_add_eq_zero]
  unfold generator
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [form, QuadraticMap.polar, Fin.sum_univ_succ, Pi.single_apply]

/-- The corrected Clifford factors have the missing distant odd sign. -/
theorem distant_differences : (generator 0 - generator 1) * (generator 2 - generator 3) =
    -((generator 2 - generator 3) * (generator 0 - generator 1)) :=
  difference_anticommute _ _ _ _
    (generator_anticommute 0 2 (by decide)) (generator_anticommute 0 3 (by decide))
    (generator_anticommute 1 2 (by decide)) (generator_anticommute 1 3 (by decide))

/-- Both Clifford differences are invertible up to the scalar two; their sign is
not explained by a zero product. -/
theorem difference_square (i j : Fin 4) (hij : i ≠ j) :
    (generator i - generator j) ^ 2 = 2 := by
  have ha := generator_square i
  have hb := generator_square j
  have hab := generator_anticommute i j hij
  rw [pow_two, sub_mul, mul_sub, mul_sub, ha, hb, hab]
  noncomm_ring
  norm_num

/-- The rational Clifford specialization is nontrivial. -/
example : Nontrivial (CliffordAlgebra form) := inferInstance

/-- The differences do not vanish in this specialization. -/
theorem difference_ne_zero (i j : Fin 4) (hij : i ≠ j) : generator i - generator j ≠ 0 := by
  intro h
  have hs := difference_square i j hij
  rw [h, zero_pow (by decide)] at hs
  have hq : (0 : ℚ) = 2 := (algebraMap ℚ (CliffordAlgebra form)).injective (by simpa only [map_zero, map_ofNat] using hs)
  norm_num at hq

/-- Concrete instance of all four parity combinations of the local crossing calculation. -/
theorem distant_parities (p q : Bool) :
    (factor (generator 0) (generator 1) p * 1) *
      (factor (generator 2) (generator 3) q * 1) =
      (if p && q then -1 else 1) *
        ((factor (generator 2) (generator 3) q * 1) *
          (factor (generator 0) (generator 1) p * 1)) :=
  distant _ _ _ _ 1 1 p q
    (generator_anticommute 0 2 (by decide)) (generator_anticommute 0 3 (by decide))
    (generator_anticommute 1 2 (by decide)) (generator_anticommute 1 3 (by decide))
    (Commute.one_left _) (Commute.one_left _) (Commute.one_left _) (Commute.one_left _)
    (Commute.refl _)

#print axioms distant
#print axioms distant_differences
#print axioms difference_square
end OddMath.QuiverHecke.CliffordExchange.Examples

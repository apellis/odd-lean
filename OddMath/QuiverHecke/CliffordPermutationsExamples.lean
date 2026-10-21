/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordPermutations
import OddMath.QuiverHecke.CliffordColoursExamples

/-! # Consumers of simultaneous colour and Clifford permutations -/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.CliffordPermutations.Examples
open CliffordColours

/-- Rational permutation operators are nonzero on the colour module. -/
theorem perm_ne_zero (w : Equiv.Perm (Fin 2)) : perm (R := ℚ) (J := Bool) w ≠ 0 := by
  intro h
  have heq : (1 : Module.End ℚ (Space ℚ Bool 2)) = 0 := by
    calc
      1 = perm (w⁻¹ * w) := by simp
      _ = perm w⁻¹ * perm w := perm_mul _ _
      _ = 0 := by rw [h, mul_zero]
  have he : e (R := ℚ) (fun _ : Fin 2 => false) = 0 := by
    calc
      _ = 1 * e (fun _ : Fin 2 => false) := (one_mul _).symm
      _ = 0 := by rw [heq, zero_mul]
  exact CliffordColours.Examples.projection_ne_zero _ he

example : perm (R := ℚ) (J := Bool) (Equiv.swap (0 : Fin 2) 1) *
    CliffordColours.C Bool.not 0 =
      CliffordColours.C Bool.not 1 * perm (Equiv.swap (0 : Fin 2) 1) := by
  simpa using perm_C (R := ℚ) (Equiv.swap (0 : Fin 2) 1) Bool.not 0

example : permK (R := ZMod 2) (Equiv.swap (0 : Fin 2) 1) (CliffordLocalization.y 0) =
    CliffordLocalization.y 1 := by simp

example (ν : Word Bool 2) :
    perm (R := ℚ) (Equiv.swap (0 : Fin 2) 1) * e ν =
      e (ν ∘ Equiv.swap (0 : Fin 2) 1) * perm (Equiv.swap (0 : Fin 2) 1) := by
  simpa using perm_e (R := ℚ) (Equiv.swap (0 : Fin 2) 1) ν

#print axioms perm_mul
#print axioms perm_C
#print axioms perm_e
#print axioms perm_scalar
#print axioms perm_ne_zero

end OddMath.QuiverHecke.CliffordPermutations.Examples

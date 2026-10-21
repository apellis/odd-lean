/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordColours
import OddMath.QuiverHecke.CliffordLocalizationExamples

/-! # Nonzero colour projections and Clifford colour transport -/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.CliffordColours.Examples

/-- Every rational two-strand colour projection has a nonzero image. -/
theorem projection_ne_zero (ν : Word Bool 2) : e (R := ℚ) ν ≠ 0 := by
  intro h
  let v := (1 : CliffordLocalization.K ℚ 2) ⊗ₜ[ℚ]
    (1 : CliffordCoefficients.Cl ℚ 2)
  have hv := congrFun (LinearMap.congr_fun h (fun _ => v)) ν
  exact CliffordLocalization.Examples.rational_vacuum_ne_zero (by simpa using hv)

/-- A nontrivial colour involution changes the Clifford source summand. -/
example (ν : Word Bool 2) : C (R := ℚ) Bool.not 0 * e ν =
    e (flip Bool.not 0 ν) * C Bool.not 0 := C_e Bool.not Bool.not_not 0 ν

example : C (R := ℚ) Bool.not (0 : Fin 2) * C Bool.not 0 = 1 :=
  C_sq Bool.not Bool.not_not 0

example : C (R := ℚ) Bool.not (0 : Fin 2) * C Bool.not 1 =
    -(C Bool.not 1 * C Bool.not 0) := C_anticommute Bool.not 0 1 (by decide)

/-- The projection decomposition is valid even over characteristic two. -/
example : (∑ ν : Word Bool 2, e (R := ZMod 2) ν) = 1 := sum_e

#print axioms C_e
#print axioms C_sq
#print axioms C_anticommute
#print axioms sum_e
#print axioms projection_ne_zero

end OddMath.QuiverHecke.CliffordColours.Examples

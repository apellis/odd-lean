import OddMath

/-! # Localized KKT coefficient consumers -/

noncomputable section
open scoped TensorProduct
open OddMath.QuiverHecke.CliffordLocalization

example : Function.Injective (scalar (R := ℚ) (n := 2)) :=
  Examples.rational_scalar_injective

example : ((1 : K ℚ 2) ⊗ₜ[ℚ] (1 : OddMath.QuiverHecke.CliffordCoefficients.Cl ℚ 2)) ≠ 0 :=
  Examples.rational_vacuum_ne_zero

example : IsUnit (y (R := ℤ) (0 : Fin 2) + y 1) := isUnit_y_add 0 1 (by decide)

example : IsUnit (y (R := ZMod 2) (0 : Fin 2) - y 1) := isUnit_y_sub 0 1 (by decide)

#print axioms OddMath.QuiverHecke.CliffordLocalization.denominator_inverses
#print axioms OddMath.QuiverHecke.CliffordLocalization.Examples.rational_scalar_injective

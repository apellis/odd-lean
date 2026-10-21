/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordLocalization
import Mathlib.RingTheory.Flat.Basic

/-! # Consumers of the localized polynomial–Clifford coefficients -/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.CliffordLocalization.Examples

private theorem tensor_unit_injective : Function.Injective
    (fun f : K ℚ 2 => f ⊗ₜ[ℚ] (1 : CliffordCoefficients.Cl ℚ 2)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := K ℚ 2)
    (Algebra.linearMap ℚ (CliffordCoefficients.Cl ℚ 2))
    (RingHom.injective (algebraMap ℚ (CliffordCoefficients.Cl ℚ 2)))
  intro f g hfg
  apply (TensorProduct.rid ℚ (K ℚ 2)).symm.injective
  apply h
  simpa using hfg

/-- Scalar operators act faithfully in the rational coefficient model. -/
theorem rational_scalar_injective : Function.Injective (scalar (R := ℚ) (n := 2)) := by
  intro f g h
  apply tensor_unit_injective
  have hv := LinearMap.congr_fun h
    ((1 : K ℚ 2) ⊗ₜ[ℚ] (1 : CliffordCoefficients.Cl ℚ 2))
  simpa using hv

/-- A nontrivial rational coefficient module. -/
theorem rational_vacuum_ne_zero :
    ((1 : K ℚ 2) ⊗ₜ[ℚ] (1 : CliffordCoefficients.Cl ℚ 2)) ≠ 0 := by
  intro h
  have heq : (1 : K ℚ 2) ⊗ₜ[ℚ] (1 : CliffordCoefficients.Cl ℚ 2) =
      (0 : K ℚ 2) ⊗ₜ[ℚ] (1 : CliffordCoefficients.Cl ℚ 2) := by simpa using h
  exact one_ne_zero (tensor_unit_injective heq)

/-- The sum denominator needs no inverse of two in the ground ring. -/
example : IsUnit (y (R := ℤ) (0 : Fin 2) + y 1) := isUnit_y_add 0 1 (by decide)

/-- Difference denominators are also valid in characteristic two. -/
example : IsUnit (y (R := ZMod 2) (0 : Fin 2) - y 1) :=
  isUnit_y_sub 0 1 (by decide)

/-- A denominator and its inverse coefficient operator. -/
example : scalar (y (R := ℚ) (0 : Fin 2) - y 1) *
    scalar (Ring.inverse (y 0 - y 1)) = 1 :=
  (denominator_inverses 0 1 (by decide)).1

/-- Localized Clifford generators anticommute on the nontrivial coefficient module. -/
example : C (R := ℚ) (0 : Fin 2) * C 1 = -(C 1 * C 0) :=
  C_anticommute 0 1 (by decide)

#print axioms algebraMap_injective
#print axioms isUnit_y_sub
#print axioms isUnit_y_add
#print axioms C_scalar
#print axioms C_anticommute
#print axioms denominator_inverses
#print axioms rational_scalar_injective
#print axioms rational_vacuum_ne_zero

end OddMath.QuiverHecke.CliffordLocalization.Examples

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NegativeColumnFunctional

/-!
# Construction of a bilinear form on the actual modified algebra

The functional from `NegativeColumnFunctional` is summed over actual diagonal
corners using finite triangular coordinates. Pairing the genuine product
`rho(x) * y` constructs a bilinear form, with both endpoint orthogonality,
left rho-adjointness, and all-negative-half-pairs normalization.

This is the construction part of the Lusztig 26.1.2 / Clark 5.2 pattern in the
library's explicit q convention over the generic covering ring. Neither finite
colours, bar consistency nor simple-root independence is used.
Nondegeneracy and the BE2 sesquilinear sigma/psi transport are not asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- The column functional evaluated on the diagonal corner of actual triangular multiplication. -/
def diagonalContraction (μ : X) :
    D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
      Coefficients.Ring where
  toFun z := negativeColumnFunctional D μ
    (one D Coefficients.q pi μ * triangularTensor D Coefficients.q pi μ z)
  map_add' _ _ := by simp [mul_add]
  map_smul' _ _ := by simp

/-- Sum the diagonal column functionals over the genuine finite coordinate support. -/
def diagonalFunctional : modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring :=
  (Finsupp.lsum Coefficients.Ring (diagonalContraction D)).comp (triangularCoordinates D)

@[simp] theorem diagonalFunctional_triangularModified (μ : X)
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    diagonalFunctional D (triangularModified D Coefficients.q pi μ z) =
      negativeColumnFunctional D μ
        (one D Coefficients.q pi μ * triangularTensor D Coefficients.q pi μ z) := by
  rw [← globalTriangular_single]
  simp only [diagonalFunctional, LinearMap.comp_apply, triangularCoordinates_globalTriangular,
    Finsupp.lsum_single, diagonalContraction]
  rfl

theorem diagonalFunctional_column (μ : X) (x : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ column D Coefficients.q pi μ) :
    diagonalFunctional D x = negativeColumnFunctional D μ
      (one D Coefficients.q pi μ * (x : CoveringUDot Coefficients.Ring D Coefficients.q pi)) := by
  obtain ⟨z, hz⟩ := triangularColumn_surjective D Coefficients.q pi μ ⟨x, hx⟩
  have he : triangularModified D Coefficients.q pi μ z = x := by
    apply Subtype.ext
    exact congrArg (fun a : column D Coefficients.q pi μ ↦ a.val) hz
  rw [← he, diagonalFunctional_triangularModified]
  rfl

/-- Different diagonal endpoints are annihilated, with no root-separation assumption. -/
theorem diagonalFunctional_offDiagonal (μ ν : X) (x : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν)
    (hne : μ ≠ ν) : diagonalFunctional D x = 0 := by
  rw [diagonalFunctional_column D ν x hx.2, one_mul_of_mem_block D Coefficients.q pi hx]
  simp [Ne.symm hne]

/-- The full bilinear form is defined on the actual nonunital modified algebra.
Its multiplication and adjoint are the existing quotient operations. -/
def modifiedForm : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi) where
  toFun x :=
    { toFun := fun y ↦ diagonalFunctional D (rhoModified D Coefficients.q pi pi_sq x * y)
      map_add' := by intro y z; simp [mul_add]
      map_smul' := by intro c y; simp [mul_smul_comm] }
  map_add' := by intro x z; ext y; simp [add_mul]
  map_smul' := by intro c x; ext y; simp [smul_mul_assoc]

@[simp] theorem modifiedForm_apply (x y : modified D Coefficients.q pi) :
    modifiedForm D x y = diagonalFunctional D (rhoModified D Coefficients.q pi pi_sq x * y) := rfl

/-- Adjointness for every actual modified element, not only Chevalley generators. -/
theorem modifiedForm_adjoint (u x y : modified D Coefficients.q pi) :
    modifiedForm D (u * x) y =
      modifiedForm D x (rhoModified D Coefficients.q pi pi_sq u * y) := by
  simp only [modifiedForm_apply, rhoModified_mul, mul_assoc]

/-- Both left and right endpoints are orthogonal. -/
theorem modifiedForm_orthogonal (μ ν μ' ν' : X) (x y : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν)
    (hy : (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈
      block D Coefficients.q pi μ' ν')
    (hne : μ ≠ μ' ∨ ν ≠ ν') : modifiedForm D x y = 0 := by
  rw [modifiedForm_apply]
  have hr := rho_mem_block D Coefficients.q pi pi_sq hx
  rcases hne with h | h
  · have hz : rhoModified D Coefficients.q pi pi_sq x * y = 0 :=
      Subtype.ext (mul_eq_zero_of_mem_block D Coefficients.q pi hr hy h)
    rw [hz, map_zero]
  · exact diagonalFunctional_offDiagonal D ν ν' _ (mul_mem_block D Coefficients.q pi hr hy) h

/-- All negative-half pairs have the original half form as normalization. -/
theorem modifiedForm_negativeHalf (μ : X) (x y : D.serreF Coefficients.q pi) :
    modifiedForm D (negativeHalf D Coefficients.q pi μ x) (negativeHalf D Coefficients.q pi μ y) =
      D.serreForm Coefficients.q pi pi_sq x y := by
  have hx : halfMap D Coefficients.q pi false μ x * one D Coefficients.q pi μ =
      halfMap D Coefficients.q pi false μ x := by
    change halfMap D Coefficients.q pi false μ x ∈ column D Coefficients.q pi μ
    simpa only [triangularTensor_tmul_one] using
      triangularTensor_mem_column D Coefficients.q pi μ (x ⊗ₜ[Coefficients.Ring] 1)
  have hy : halfMap D Coefficients.q pi false μ y * one D Coefficients.q pi μ =
      halfMap D Coefficients.q pi false μ y := by
    change halfMap D Coefficients.q pi false μ y ∈ column D Coefficients.q pi μ
    simpa only [triangularTensor_tmul_one] using
      triangularTensor_mem_column D Coefficients.q pi μ (y ⊗ₜ[Coefficients.Ring] 1)
  have hr : one D Coefficients.q pi μ *
      (rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi false μ x)).unop =
      (rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi false μ x)).unop := by
    simpa only [rho_mul, rho_one] using congrArg (fun z ↦ (rho D Coefficients.q pi pi_sq z).unop) hx
  rw [modifiedForm_apply, diagonalFunctional_column D μ _ (by
    change ((rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi false μ x)).unop *
      halfMap D Coefficients.q pi false μ y) * one D Coefficients.q pi μ = _
    rw [mul_assoc, hy]
    rfl)]
  change negativeColumnFunctional D μ
    (one D Coefficients.q pi μ * ((rho D Coefficients.q pi pi_sq
      (halfMap D Coefficients.q pi false μ x)).unop * halfMap D Coefficients.q pi false μ y)) = _
  rw [← mul_assoc, hr, negativeColumnFunctional_rho_halfMap]

end OddMath.CoveringQuantum.UDot.GenericTensor

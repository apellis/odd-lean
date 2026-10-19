/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TriangularRetraction
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Global triangular coordinates on the modified algebra

The actual nonunital modified algebra is linearly equivalent to finitely supported
right-weight families of tensors of the two Serre halves. The coefficient at `μ`
is concrete tensor evaluation of the right-column component `x * 1_μ`.
This provides coordinates for constructing forms and an equality criterion using
the existing family of tensor representations. No individual representation is
asserted faithful, and no full modified form or integral basis is constructed.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- Sum the genuine matched triangular products at finitely many right weights. -/
def globalTriangular :
    (X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) →ₗ[
      Coefficients.Ring] modified D Coefficients.q pi :=
  Finsupp.lsum Coefficients.Ring (triangularModified D Coefficients.q pi)

@[simp] theorem globalTriangular_single (μ : X)
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    globalTriangular D (Finsupp.single μ z) = triangularModified D Coefficients.q pi μ z :=
  Finsupp.lsum_single _ _ _ _

/-- Right multiplication by a weight idempotent selects precisely that column. -/
theorem triangularTensor_mul_one (μ η : X)
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    triangularTensor D Coefficients.q pi μ z * one D Coefficients.q pi η =
      if μ = η then triangularTensor D Coefficients.q pi μ z else 0 := by
  have hx := triangularTensor_mem_column D Coefficients.q pi μ z
  change triangularTensor D Coefficients.q pi μ z * one D Coefficients.q pi μ = _ at hx
  conv_lhs => rw [← hx]
  rw [mul_assoc, one_mul_one]
  split_ifs with h
  · exact hx
  · exact mul_zero _

/-- An arbitrary finite inhomogeneous family recovers its actual right column. -/
theorem globalTriangular_mul_one
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) (μ : X) :
    (globalTriangular D f : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
      one D Coefficients.q pi μ = triangularTensor D Coefficients.q pi μ (f μ) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simpa only [map_add, NonUnitalSubalgebra.coe_add, add_mul, Finsupp.add_apply]
      using congrArg₂ (· + ·) hf hg
  | single η z =>
    rw [globalTriangular_single]
    change triangularTensor D Coefficients.q pi η z * _ = _
    rw [triangularTensor_mul_one]
    by_cases h : η = μ
    · subst η; simp
    · simp [h, Finsupp.single_eq_of_ne (Ne.symm h)]

/-- The coordinate functions have finite support, as a consequence of finite local units. -/
theorem finite_coordinate_support (x : modified D Coefficients.q pi) :
    (Function.support (fun μ ↦ tensorEval D μ
      ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
        one D Coefficients.q pi μ))).Finite := by
  obtain ⟨s, _, hs⟩ := exists_localUnit D Coefficients.q pi x.property
  apply s.finite_toSet.subset
  intro μ hμ
  by_contra hn
  have hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
      one D Coefficients.q pi μ = 0 := by
    calc
      _ = ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
          ∑ η ∈ s, one D Coefficients.q pi η) * one D Coefficients.q pi μ := by rw [hs]
      _ = 0 := by
        rw [mul_assoc, Finset.sum_mul]
        have hz : ∑ η ∈ s, one D Coefficients.q pi η * one D Coefficients.q pi μ = 0 := by
          apply Finset.sum_eq_zero
          intro η hη
          have hne : η ≠ μ := fun h ↦ hn (h ▸ hη)
          simp [one_mul_one, hne]
        rw [hz, mul_zero]
  exact hμ (by dsimp; rw [hx, map_zero])

/-- Explicit finitely supported inverse: evaluate each actual right-column component. -/
def triangularCoordinates : modified D Coefficients.q pi →ₗ[Coefficients.Ring]
    (X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) where
  toFun x := Finsupp.ofSupportFinite (fun μ ↦ tensorEval D μ
    ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) * one D Coefficients.q pi μ))
    (finite_coordinate_support D x)
  map_add' x y := by ext μ; simp [add_mul]
  map_smul' c x := by ext μ; simp

@[simp] theorem triangularCoordinates_apply (x : modified D Coefficients.q pi) (μ : X) :
    triangularCoordinates D x μ = tensorEval D μ
      ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) * one D Coefficients.q pi μ) := rfl

/-- First roundtrip, on all finite families of arbitrary tensors. -/
@[simp] theorem triangularCoordinates_globalTriangular
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    triangularCoordinates D (globalTriangular D f) = f := by
  ext μ
  rw [triangularCoordinates_apply, globalTriangular_mul_one, tensorEval_triangularTensor]

/-- Every actual modified element is a finite sum of matched triangular products. -/
theorem globalTriangular_surjective : Function.Surjective (globalTriangular D) := by
  intro x
  let L := (modified D Coefficients.q pi).toSubmodule.subtype.comp (globalTriangular D)
  have hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ LinearMap.range L := by
    refine Submodule.iSup_induction (fun b : X × X ↦ block D Coefficients.q pi b.1 b.2)
      (motive := fun y ↦ y ∈ LinearMap.range L) x.property ?_ ?_ ?_
    · intro b y hy
      obtain ⟨z, hz⟩ := triangularColumn_surjective D Coefficients.q pi b.2 ⟨y, hy.2⟩
      refine ⟨Finsupp.single b.2 z, ?_⟩
      change (globalTriangular D (Finsupp.single b.2 z) :
        CoveringUDot Coefficients.Ring D Coefficients.q pi) = y
      rw [globalTriangular_single]
      exact congrArg Subtype.val hz
    · exact Submodule.zero_mem _
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz
  obtain ⟨f, hf⟩ := hx
  exact ⟨f, Subtype.ext hf⟩

/-- Second roundtrip, on the actual nonunital modified algebra. -/
@[simp] theorem globalTriangular_triangularCoordinates (x : modified D Coefficients.q pi) :
    globalTriangular D (triangularCoordinates D x) = x := by
  obtain ⟨f, rfl⟩ := globalTriangular_surjective D x
  rw [triangularCoordinates_globalTriangular]

/-- Recover the actual right-weight component from its tensor coordinate. -/
theorem triangularTensor_coordinates (x : modified D Coefficients.q pi) (μ : X) :
    triangularTensor D Coefficients.q pi μ (triangularCoordinates D x μ) =
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) * one D Coefficients.q pi μ := by
  rw [← globalTriangular_mul_one, globalTriangular_triangularCoordinates]

/-- On a column, the global inverse is exactly the accepted fixed-column inverse. -/
theorem triangularCoordinates_column (μ : X) (x : column D Coefficients.q pi μ) :
    triangularCoordinates D
      ⟨x, column_le_modified D Coefficients.q pi μ x.property⟩ μ =
        (triangularColumnEquiv D μ).symm x := by
  rw [triangularCoordinates_apply, triangularColumnEquiv_symm_apply]
  change tensorEval D μ ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
    one D Coefficients.q pi μ) = _
  rw [x.property]

/-- Global triangular decomposition, excluding the scalar identity of the unital envelope. -/
def globalTriangularEquiv :
    (X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) ≃ₗ[
      Coefficients.Ring] modified D Coefficients.q pi :=
  { globalTriangular D with
    invFun := triangularCoordinates D
    left_inv := triangularCoordinates_globalTriangular D
    right_inv := globalTriangular_triangularCoordinates D }

@[simp] theorem globalTriangularEquiv_apply
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    globalTriangularEquiv D f = globalTriangular D f := rfl

@[simp] theorem globalTriangularEquiv_symm_apply (x : modified D Coefficients.q pi) :
    (globalTriangularEquiv D).symm x = triangularCoordinates D x := rfl

/-- A coordinate is the vacuum value of the existing modified tensor representation. -/
theorem triangularCoordinates_eq_vacuum (x : modified D Coefficients.q pi) (μ : X) :
    triangularCoordinates D x μ =
      modifiedRepresentation D μ x (1 ⊗ₜ[Coefficients.Ring] 1) := by
  rw [triangularCoordinates_apply]
  change representation D μ ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
    one D Coefficients.q pi μ) (1 ⊗ₜ[Coefficients.Ring] 1) = _
  rw [map_mul, Module.End.mul_apply, representation_one, weightProject_vacuum]
  rfl

/-- The existing family, indexed by all right weights, jointly separates modified elements. -/
theorem modifiedRepresentation_jointly_injective :
    Function.Injective (fun x : modified D Coefficients.q pi ↦
      fun μ ↦ modifiedRepresentation D μ x) := by
  intro x y h
  apply (globalTriangularEquiv D).symm.injective
  change triangularCoordinates D x = triangularCoordinates D y
  ext μ
  rw [triangularCoordinates_eq_vacuum, triangularCoordinates_eq_vacuum]
  exact congrArg (fun f ↦ f (1 ⊗ₜ[Coefficients.Ring] 1)) (congrFun h μ)

/-- Equality in the actual algebra can be tested in all the constructed tensor representations. -/
theorem eq_iff_modifiedRepresentation (x y : modified D Coefficients.q pi) :
    x = y ↔ ∀ μ, modifiedRepresentation D μ x = modifiedRepresentation D μ y := by
  constructor
  · rintro rfl μ; rfl
  · intro h
    exact modifiedRepresentation_jointly_injective D (funext h)

end OddMath.CoveringQuantum.UDot.GenericTensor

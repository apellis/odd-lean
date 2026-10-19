/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.Triangular
import OddMath.CoveringQuantum.UDot.HalfEmbeddings
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Matched triangular tensor multiplication

The right action on column sections extends the matched negative-positive product
linearly to the tensor product of the two actual Serre halves. The intermediate
weight is determined by the positive degree, not an extra tensor parameter.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot
open MulOpposite TensorProduct
variable {k I X : Type*} [CommRing k] [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- The section consisting of the negative half at every right weight. -/
def negativeSection : D.serreF q π →ₗ[k] (∀ μ, column D q π μ) where
  toFun x := unop (halfAction D q π false x) (weightUnits D q π)
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem negativeSection_value (x : D.serreF q π) (μ : X) :
    sectionValue D q π (negativeSection D q π x) μ = halfMap D q π false μ x := rfl

/-- Matched multiplication on both full, ungraded Serre halves. -/
def triangularBilinear (μ : X) :
    D.serreF q π →ₗ[k] D.serreF q π →ₗ[k] CoveringUDot k D q π where
  toFun x := (sectionEval D q π (negativeSection D q π x) μ).comp
    (halfAction D q π true).toLinearMap
  map_add' x y := by
    ext z
    simp [LinearMap.comp_apply, sectionEval, sectionValue]
  map_smul' c x := by
    ext z
    simp [LinearMap.comp_apply, sectionEval, sectionValue]

/-- Genuine triangular multiplication at fixed right weight. No grading restriction
is imposed on either tensor factor. -/
def triangularTensor (μ : X) :
    D.serreF q π ⊗[k] D.serreF q π →ₗ[k] CoveringUDot k D q π :=
  TensorProduct.lift (triangularBilinear D q π μ)

/-- On a homogeneous positive input this is precisely multiplication of the existing
half maps at the uniquely matching intermediate weight. -/
theorem triangularTensor_homogeneous (μ : X) (x : D.serreF q π)
    {ν : I →₀ ℕ} {y : D.serreF q π} (hy : y ∈ halfWeightSpace D q π ν) :
    triangularTensor D q π μ (x ⊗ₜ[k] y) =
      halfMap D q π false (μ + halfWeight D true ν) x * halfMap D q π true μ y := by
  exact halfAction_homogeneous D q π true hy (negativeSection D q π x) μ

/-- The full tensor map agrees with the existing matched normal words. -/
@[simp] theorem triangularTensor_monomial (μ : X) (a b : List I) :
    triangularTensor D q π μ
      (D.toSerreF q π (PreF.monomial k a) ⊗ₜ[k] D.toSerreF q π (PreF.monomial k b)) =
      normalWord D q π a b μ := by
  change sectionEval D q π (negativeSection D q π _) μ
    (halfAction D q π true (D.toSerreF q π (PreF.monomial k b))) = _
  rw [halfAction_toSerreF, halfActionFree_monomial, negativeSection_value, halfMap_monomial]
  rfl

@[simp] theorem triangularTensor_tmul_one (μ : X) (x : D.serreF q π) :
    triangularTensor D q π μ (x ⊗ₜ[k] 1) = halfMap D q π false μ x := by
  change sectionEval D q π (negativeSection D q π x) μ (halfAction D q π true 1) = _
  simp [sectionEval, sectionValue, negativeSection, halfMap]

@[simp] theorem triangularTensor_one_tmul (μ : X) (y : D.serreF q π) :
    triangularTensor D q π μ (1 ⊗ₜ[k] y) = halfMap D q π true μ y := by
  change sectionEval D q π (negativeSection D q π 1) μ _ = _
  have h : negativeSection D q π 1 = weightUnits D q π := by
    ext η
    simp [negativeSection]
  rw [h]
  rfl

/-- A mixed simple tensor has the correctly shifted negative generator. -/
theorem triangularTensor_θ_θ (μ : X) (i j : I) :
    triangularTensor D q π μ
      (D.toSerreF q π (PreF.θ k i) ⊗ₜ[k] D.toSerreF q π (PreF.θ k j)) =
      F D q π i (μ + D.α j) * E D q π j μ := by
  have h := triangularTensor_monomial D q π μ [i] [j]
  simpa [PreF.monomial_cons, PreF.monomial_nil, normalWord, halfWord, halfGen,
    PreF.wordWeight_cons, PreF.wordWeight_nil, halfRoot, F_mul_one_self, E_mul_one_self] using h

/-- Every value has the specified right weight. -/
theorem triangularTensor_mem_column (μ : X) (z : D.serreF q π ⊗[k] D.serreF q π) :
    triangularTensor D q π μ z ∈ column D q π μ := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    exact (unop (halfAction D q π true y) (negativeSection D q π x) μ).property
  | add x y hx hy => simpa only [map_add] using (column D q π μ).add_mem hx hy

/-- The matched product, with its actual right-column codomain. -/
def triangularColumn (μ : X) :
    D.serreF q π ⊗[k] D.serreF q π →ₗ[k] column D q π μ :=
  (triangularTensor D q π μ).codRestrict _ (triangularTensor_mem_column D q π μ)

/-- The entire right column belongs to the actual nonunital modified algebra. -/
theorem column_le_modified (μ : X) :
    column D q π μ ≤ (modified D q π).toSubmodule := by
  intro x hx
  rw [← triangularSpan_eq_modified, ← hx]
  exact mul_one_mem_triangularSpan D q π x μ

private theorem halfWords_mul_one_mem_range (a b : List I) (ν η μ : X) :
    (halfWord D q π false a ν * halfWord D q π true b η) * one D q π μ ∈
      LinearMap.range (triangularTensor D q π μ) := by
  rw [mul_assoc, mul_one_of_mem_block D q π (halfWord_mem_block D q π true b η)]
  split_ifs with h
  · subst η
    by_cases hm : ν = μ + halfWeight D true (PreF.wordWeight b)
    · subst ν
      exact ⟨D.toSerreF q π (PreF.monomial k a) ⊗ₜ[k]
        D.toSerreF q π (PreF.monomial k b), triangularTensor_monomial D q π μ a b⟩
    · rw [mul_eq_zero_of_mem_block D q π (halfWord_mem_block D q π false a ν)
        (halfWord_mem_block D q π true b μ) hm]
      exact Submodule.zero_mem _
  · rw [mul_zero]
    exact Submodule.zero_mem _

/-- Spanning gives surjectivity onto the full fixed right column, with no freely
varying intermediate weight in the tensor domain. -/
theorem range_triangularTensor (μ : X) :
    LinearMap.range (triangularTensor D q π μ) = column D q π μ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact triangularTensor_mem_column D q π μ z
  · intro x hx
    have hs : x ∈ triangularSpan D q π := by
      rw [← hx]
      exact mul_one_mem_triangularSpan D q π x μ
    have hm : x * one D q π μ ∈ LinearMap.range (triangularTensor D q π μ) := by
      clear hx
      induction hs using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, b, ν, η, rfl⟩ := hz
        exact halfWords_mul_one_mem_range D q π a b ν η μ
      | zero => simpa only [zero_mul] using (LinearMap.range (triangularTensor D q π μ)).zero_mem
      | add z w hz hw ihz ihw =>
        rw [add_mul]
        exact Submodule.add_mem _ ihz ihw
      | smul c z hz ih =>
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ c ih
    rwa [hx] at hm

/-- The actual matched tensor multiplication is onto the right column. -/
theorem triangularColumn_surjective (μ : X) :
    Function.Surjective (triangularColumn D q π μ) := by
  intro x
  have hx : (x : CoveringUDot k D q π) ∈ LinearMap.range (triangularTensor D q π μ) := by
    rw [range_triangularTensor]
    exact x.property
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, Subtype.ext hz⟩

/-- The same genuine multiplication with values in the modified algebra. -/
def triangularModified (μ : X) :
    D.serreF q π ⊗[k] D.serreF q π →ₗ[k] modified D q π :=
  (triangularTensor D q π μ).codRestrict _ fun z ↦
    column_le_modified D q π μ (triangularTensor_mem_column D q π μ z)

section Generic
open Coefficients PreF

/-- A mixed tensor has an explicit action in the already constructed representation:
its positive generator contracts a simple negative vector, then its negative
generator creates the output. This is an evaluation identity, not faithfulness. -/
theorem representation_triangularTensor_θ_θ (Λ : X) (i j : I) :
    GenericVerma.representation D Λ
      (triangularTensor D Coefficients.q pi (Λ - D.α j)
        (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) ⊗ₜ[Coefficients.Ring]
          D.toSerreF Coefficients.q pi (θ Coefficients.Ring j)))
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring j)) =
      qpInt (D.qi Coefficients.q j) (D.pii pi j) (D.h j Λ) •
        D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) := by
  rw [triangularTensor_θ_θ, sub_add_cancel, map_mul, Module.End.mul_apply,
    GenericVerma.representation_E, Module.End.mul_apply]
  have hp : GenericVerma.weightProject D Λ (Λ - D.α j)
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring j)) =
      D.toSerreF Coefficients.q pi (θ Coefficients.Ring j) := by
    rw [GenericVerma.weightProject_mk]
    have h := weightProjectFree_monomial (k := Coefficients.Ring) D Λ (Λ - D.α j) [j]
    simp only [monomial_cons, monomial_nil, mul_one, wordWeight_cons, wordWeight_nil,
      add_zero, halfWeight_single, halfRoot, ite_true, sub_sub_cancel] at h
    rw [h]
  rw [hp, GenericVerma.lower_θ_self, map_smul, GenericVerma.representation_F]
  have hu : GenericVerma.weightProject D Λ Λ (1 : D.serreF Coefficients.q pi) = 1 := by
    rw [← map_one (D.toSerreF Coefficients.q pi), GenericVerma.weightProject_mk]
    change D.toSerreF Coefficients.q pi
      (weightProjectFree D Λ Λ (monomial Coefficients.Ring [])) = _
    rw [weightProjectFree_monomial]
    simp only [wordWeight_nil, halfWeight_zero, sub_self, ite_true, monomial_nil]
  rw [hu, mul_one]

end Generic
end OddMath.CoveringQuantum.UDot

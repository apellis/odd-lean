/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.CyclicFiltration

/-! Genuine formal-degree projections on the original Serre quotient.
Descent uses the established half-form radical identification, not root-image
independence or the image submodule definition of halfWeightSpace. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

/-- Formal degree, before any root-to-weight map. -/
def degreeFree (ν : I →₀ ℕ) : Module.End Coefficients.Ring (PreF Coefficients.Ring I) where
  toFun x := (gradingHom Coefficients.Ring I x).coeff ν
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem degreeFree_word (ν : I →₀ ℕ) (w : List I) :
    degreeFree ν (monomial Coefficients.Ring w) =
      if wordWeight w = ν then monomial Coefficients.Ring w else 0 := by
  simp [degreeFree, gradingHom_monomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Orthogonality in formal degrees makes every degree projection self-adjoint. -/
theorem degreeFree_form (χ : Bichar Coefficients.Ring I) (nm : I → Coefficients.Ring)
    (ν : I →₀ ℕ) (x y : PreF Coefficients.Ring I) :
    form χ nm (degreeFree ν x) y = form χ nm x (degreeFree ν y) := by
  induction x using induction_monomial with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | smul c x hx => simp [hx]
  | word w =>
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | smul c y hy => simp only [map_smul, hy]
    | word v =>
      by_cases h : wordWeight w = wordWeight v
      · simp only [degreeFree_word, h]
        split_ifs <;> simp
      · have hz := form_eq_zero_of_ne χ nm h
          (monomial_mem_weightSpace (k := Coefficients.Ring) w)
          (monomial_mem_weightSpace (k := Coefficients.Ring) v)
        simp only [degreeFree_word]
        split_ifs <;> simp [hz]

variable (hD : D.toSuperCartanDatum.BarConsistent)

omit [DecidableEq I] in
include hD in
/-- Formal-degree projection preserves the actual Serre ideal. -/
theorem degreeFree_mem_serreIdeal (ν : I →₀ ℕ) {x : PreF Coefficients.Ring I}
    (hx : x ∈ D.serreIdeal Coefficients.q pi) :
    degreeFree ν x ∈ D.serreIdeal Coefficients.q pi := by
  classical
  rw [serreIdeal_eq_radical D.toSuperCartanDatum hD] at hx ⊢
  rw [mem_radical_iff] at hx ⊢
  intro y
  rw [degreeFree_form]
  exact hx _

/-- A descended formal-degree projection on H itself, not a weight-image projector. -/
def degree (ν : I →₀ ℕ) : Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  let p := (D.toSerreF Coefficients.q pi).toLinearMap
  let f := p.comp (degreeFree ν)
  ((LinearMap.ker p).liftQ f (by
    intro x hx
    change D.toSerreF Coefficients.q pi (degreeFree ν x) = 0
    apply (D.mem_serreIdeal Coefficients.q pi _).mp
    apply degreeFree_mem_serreIdeal D hD ν
    exact (D.mem_serreIdeal Coefficients.q pi x).mpr hx)).comp
    (p.quotKerEquivOfSurjective (D.toSerreF_surjective Coefficients.q pi)).symm.toLinearMap

omit [DecidableEq I] in
@[simp] theorem degree_mk (ν : I →₀ ℕ) (x : PreF Coefficients.Ring I) :
    degree D hD ν (D.toSerreF Coefficients.q pi x) =
      D.toSerreF Coefficients.q pi (degreeFree ν x) := by
  let p := (D.toSerreF Coefficients.q pi).toLinearMap
  simp only [degree, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (LinearMap.ker p).liftQ _ _ ((p.quotKerEquivOfSurjective _).symm (p x)) = _
  exact congrArg ((LinearMap.ker p).liftQ _ _)
    (p.quotKerEquivOfSurjective_symm_apply (D.toSerreF_surjective Coefficients.q pi) x)

@[simp] theorem degree_word (ν : I →₀ ℕ) (w : List I) :
    degree D hD ν (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
      if wordWeight w = ν then
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) else 0 := by
  rw [degree_mk, degreeFree_word]
  split_ifs <;> simp

/-- Formal bidegree projection on actual Serre tensors. -/
def bidegree (α β : I →₀ ℕ) : Module.End Coefficients.Ring
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  TensorProduct.map (degree D hD α) (degree D hD β)

@[simp] theorem bidegree_wordTensor (α β : I →₀ ℕ) (a b : List I) :
    bidegree D hD α β (wordTensor D a b) =
      if wordWeight a = α ∧ wordWeight b = β then wordTensor D a b else 0 := by
  simp only [bidegree, wordTensor, TensorProduct.map_tmul, degree_word]
  split_ifs <;> simp_all

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic

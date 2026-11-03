/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedMixedCross
import OddMath.QuiverHecke.CyclotomicAction.ELVRestrictionCoendCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleInverse

/-! # The prescribed distinct mate through coefficient truncation

Brundan–Ellis (1.12): retain the positive old crossing under the selected
append quotient comparison, with the genuine restriction-square inverse
on its source. Ordinary coefficient coordinates are changed before the
old and truncated coends are composed. No flatness assumption is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i j : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Oi" => append D Sc cutoff i
local notation "Oj" => append D Sc cutoff j
local notation "Ti" => truncatedAppend D Sc cutoff N [i]
local notation "Tj" => truncatedAppend D Sc cutoff N [j]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "R" => CategoryTheory.Functor.obj (BalancedInduction.restriction Oj) RM
local notation "L" => CategoryTheory.Functor.obj (BalancedInduction.restriction Tj) M
local notation "e" => CategoryTheory.Iso.symm (weightedAppendRestrictionIso D Sc cutoff N j M)

private theorem conjugate_equiv_forward
    {V U W Z : Type u} [AddCommMonoid V] [Module k V]
    [AddCommMonoid U] [Module k U] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Z] [Module k Z]
    (a : V ≃ₗ[k] U) (f : V ≃ₗ[k] W) (b : W ≃ₗ[k] Z) (g : U →ₗ[k] Z)
    (h : b.toLinearMap ∘ₗ f.toLinearMap = g ∘ₗ a.toLinearMap) :
    ((a.symm.trans f).trans b).toLinearMap = g := by
  ext x
  obtain ⟨y, rfl⟩ := a.surjective x
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hy

/-- The old and truncated mixed source coends are compared by chosen isomorphisms. -/
def truncatedDistinctSourceEquiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi ((Oj) ⋙ (RM).toFunctor) w ≃ₗ[k]
      BalancedInduction.Obj Ti ((Tj) ⋙ M.toFunctor) ((Q).obj w) :=
  ((BalancedInduction.restrictionCoendCoordinates Oi Oj RM w).symm.trans
    (weightedAppendSourceLinearEquiv D Sc cutoff N i R L e w)).trans
      (BalancedInduction.restrictionCoendCoordinates Ti Tj M ((Q).obj w))

/-- Its forward map retains the selected quotient chart and the even restriction square. -/
def truncatedDistinctSourceLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi ((Oj) ⋙ (RM).toFunctor) w →ₗ[k]
      BalancedInduction.Obj Ti ((Tj) ⋙ M.toFunctor) ((Q).obj w) :=
  (BalancedInduction.restrictionCoendCoordinates Ti Tj M ((Q).obj w)).toLinearMap ∘ₗ
    weightedAppendSourceLinear D Sc cutoff N i R L (e).hom w ∘ₗ
      (BalancedInduction.restrictionCoendCoordinates Oi Oj RM w).symm.toLinearMap

/-- The source chart is a genuine linear equivalence of the specified mixed coends. -/
theorem truncatedDistinctSourceEquiv_hom (w : OldCategory D Sc cutoff) :
    (truncatedDistinctSourceEquiv D Sc cutoff N i j M w).toLinearMap =
      truncatedDistinctSourceLinear D Sc cutoff N i j M w := by
  rw [truncatedDistinctSourceEquiv, LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    weightedAppendSourceLinearEquiv_hom D Sc cutoff N i R L e
      (weightedAppendRestrictionIso_inv_mem D Sc cutoff N j M) w]
  rfl

/-- Every whole coefficient arrow is sent to its literal quotient, with its vector unchanged. -/
theorem truncatedDistinctSourceLinear_tensor (s w : OldCategory D Sc cutoff)
    (g : (Oi).obj s ⟶ w) (b : (RM).obj ((Oj).obj s)) :
    truncatedDistinctSourceLinear D Sc cutoff N i j M w
      (BalancedInduction.tensor Oi ((Oj) ⋙ (RM).toFunctor) s g b) =
      BalancedInduction.tensor Ti ((Tj) ⋙ M.toFunctor) ((Q).obj s) ((Q).map g) b := by
  rw [truncatedDistinctSourceLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    BalancedInduction.restrictionCoendCoordinates_inv_tensor,
    weightedAppendSourceLinear_tensor]
  have hb : (e).hom.app 0 s b = b := rfl
  rw [hb]
  exact BalancedInduction.restrictionCoendCoordinates_hom_tensor Ti Tj M
    ((Q).obj s) ((Q).obj w) ((Q).map g) b

/-- The target chart is the same selected i-append comparison at the j-output word. -/
def truncatedDistinctTargetEquiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi (RM).toFunctor ((Oj).obj w) ≃ₗ[k]
      BalancedInduction.Obj Ti M.toFunctor ((Tj).obj ((Q).obj w)) :=
  weightedAppendLinearEquiv D Sc cutoff N i M ((Oj).obj w)

/-- The target forward map is the selected quotient comparison at the j-output. -/
def truncatedDistinctTargetLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Oi (RM).toFunctor ((Oj).obj w) →ₗ[k]
      BalancedInduction.Obj Ti M.toFunctor ((Tj).obj ((Q).obj w)) :=
  weightedAppendComparisonLinear D Sc cutoff N i M ((Oj).obj w)

theorem truncatedDistinctTargetEquiv_hom (w : OldCategory D Sc cutoff) :
    (truncatedDistinctTargetEquiv D Sc cutoff N i j M w).toLinearMap =
      truncatedDistinctTargetLinear D Sc cutoff N i j M w := rfl

/-- Quotienting retains the full target coefficient arrow and input vector. -/
theorem truncatedDistinctTargetLinear_tensor
    (s w : OldCategory D Sc cutoff) (g : (Oi).obj ((Oj).obj s) ⟶ (Oj).obj w)
    (b : (RM).obj ((Oj).obj s)) :
    truncatedDistinctTargetLinear D Sc cutoff N i j M w
      (BalancedInduction.tensor Oi (RM).toFunctor ((Oj).obj s) g b) =
      BalancedInduction.tensor Ti M.toFunctor ((Q).obj ((Oj).obj s)) ((Q).map g) b :=
  appendWeightedModuleIso_hom_tensor D Sc cutoff N i M ((Oj).obj s) ((Oj).obj w) g b

private theorem quotient_map_append (s w : OldCategory D Sc cutoff) (f : s ⟶ w) :
    (Q).map ((Oj).map f) = (Tj).map ((Q).map f) := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff s.word w.word).mkQ_surjective f
  rfl

/-- The positive mixed coefficient projects with its entire parity twist. -/
theorem truncatedDistinctMate_coefficient
    (s w : OldCategory D Sc cutoff) (g : (Oi).obj s ⟶ w) :
    (Q).map (Distinct.crossComponent D Sc cutoff i j s ≫
      twist k (D.parity i * D.parity j) ((Oj).map g)) =
      truncatedDistinctCrossComponent D Sc cutoff N i j ((Q).obj s) ≫
        twist k (D.parity i * D.parity j) ((Tj).map ((Q).map g)) := by
  rw [Functor.map_comp, map_twist, oldTruncateFunctor_map_distinctCross, quotient_map_append]
  rfl

private theorem quotient_append_obj (a : I) (s : OldCategory D Sc cutoff) :
    (Q).obj ((append D Sc cutoff a).obj s) =
      (truncatedAppend D Sc cutoff N [a]).obj ((Q).obj s) := rfl

/-- The whole prescribed positive distinct mate commutes with the selected quotient charts. -/
theorem truncatedDistinctMateLinear_square (w : OldCategory D Sc cutoff) :
    truncatedDistinctTargetLinear D Sc cutoff N i j M w ∘ₗ
        Distinct.moduleMateLinear D Sc cutoff i j RM w =
      BalancedInduction.orderedMixedMateCoend Ti Tj
        (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj w) ∘ₗ
          truncatedDistinctSourceLinear D Sc cutoff N i j M w := by
  apply BalancedInduction.hom_ext
  intro s g b
  have hOld := Distinct.moduleMateLinear_tensor D Sc cutoff i j RM s w g b
  generalize hc : (Distinct.crossComponent D Sc cutoff i j s ≫
    twist k (D.parity i * D.parity j) ((Oj).map g)) = c' at hOld
  have hLeft := congrArg (truncatedDistinctTargetLinear D Sc cutoff N i j M w) hOld
  have hTarget := truncatedDistinctTargetLinear_tensor D Sc cutoff N i j M s w c' b
  have hSource := truncatedDistinctSourceLinear_tensor D Sc cutoff N i j M s w g b
  have hRight := congrArg
    (BalancedInduction.orderedMixedMateCoend Ti Tj
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj w)) hSource
  have hNew := BalancedInduction.orderedMixedMateCoend_tensor (k := k) Ti Tj
    (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj s) ((Q).obj w) ((Q).map g) b
  have hCoef := (congrArg (fun f => (Q).map f) hc).symm.trans
    (truncatedDistinctMate_coefficient D Sc cutoff N i j s w g)
  have hTensor := congrArg (fun a => BalancedInduction.tensor Ti M.toFunctor
    ((Tj).obj ((Q).obj s)) a b) hCoef
  simp only [quotient_append_obj] at hTarget
  simp only [LinearMap.comp_apply]
  exact (hLeft.trans (hTarget.trans hTensor)).trans (hRight.trans hNew).symm

/-- The explicit decoder is the old PBW inverse between the selected quotient charts. -/
def truncatedDistinctMateEquivAtOld (hij : i ≠ j) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Ti (Tj ⋙ M.toFunctor) ((Q).obj w) ≃ₗ[k]
      BalancedInduction.Obj Ti M.toFunctor ((Tj).obj ((Q).obj w)) :=
  ((truncatedDistinctSourceEquiv D Sc cutoff N i j M w).symm.trans
    (Distinct.moduleMateUnderlyingEquiv D Sc cutoff i j hij RM w)).trans
      (truncatedDistinctTargetEquiv D Sc cutoff N i j M w)

/-- Its forward map is the prescribed positive cup-crossing-cap on every vector. -/
theorem truncatedDistinctMateEquivAtOld_hom (hij : i ≠ j) (w : OldCategory D Sc cutoff) :
    (truncatedDistinctMateEquivAtOld D Sc cutoff N i j M hij w).toLinearMap =
      BalancedInduction.orderedMixedMateCoend Ti Tj
        (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj w) := by
  apply conjugate_equiv_forward
  rw [truncatedDistinctSourceEquiv_hom, truncatedDistinctTargetEquiv_hom,
    Distinct.moduleMateUnderlyingEquiv_toLinearMap]
  exact truncatedDistinctMateLinear_square D Sc cutoff N i j M w

/-- The prescribed mixed mate is bijective on every quotient object. -/
theorem truncatedDistinctMate_bijective (hij : i ≠ j)
    (w : TruncatedCategory D Sc cutoff N) :
    Function.Bijective (BalancedInduction.orderedMixedMateCoend Ti Tj
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) M w) := by
  have h : Function.Bijective (BalancedInduction.orderedMixedMateCoend Ti Tj
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) M ((Q).obj ⟨w.word⟩)) := by
    rw [← truncatedDistinctMateEquivAtOld_hom D Sc cutoff N i j M hij ⟨w.word⟩]
    exact (truncatedDistinctMateEquivAtOld D Sc cutoff N i j M hij ⟨w.word⟩).bijective
  have hw : (Q).obj (⟨w.word⟩ : OldCategory D Sc cutoff) = w := by cases w; rfl
  rw [hw] at h
  exact h

end OddMath.QuiverHecke.ELVOld

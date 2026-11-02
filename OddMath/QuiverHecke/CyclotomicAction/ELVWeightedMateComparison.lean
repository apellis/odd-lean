import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateEvaluation

/-! # Ordered mate through the weighted quotient

DeformedMatrixComparison (2), (4) compares the prescribed cup-crossing-cap
mate. Its existing tensor evaluation retains the signed crossing and the
ordinary adjunction maps. The canonical restriction square identifies the
source of the selected append comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
section MateCarriers
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))

/-- The prescribed ordered mate on its literal restricted-module coend. -/
def orderedMateLinear (w : C) :
    BalancedInduction.Obj A ((BalancedInduction.restriction A).obj M).toFunctor w →ₗ[k]
      BalancedInduction.Obj A M.toFunctor (A.obj w) :=
  (BalancedInduction.orderedMateComponent A hα M).total w

/-- The extra minus and the whole arrow twist of the ordered mate. -/
theorem orderedMateLinear_tensor (s w : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    orderedMateLinear A hα M w
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      -BalancedInduction.tensor A M.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b :=
  BalancedInduction.orderedMateComponent_total_tensor A hα M s w g b
end MateCarriers

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The old Rouquier mate is the given component of `oldModuleMate`. -/
def weightedOldMateLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj J (RM).toFunctor ((J).obj w) :=
  ((CyclotomicCrossingTensor.oldModuleMate D Sc cutoff i).app
    (D.parity i * D.parity i) RM).total w

theorem weightedOldMateLinear_tensor (s w : OldCategory D Sc cutoff)
    (g : (J).obj s ⟶ w) (b : M.obj ((Q).obj ((J).obj s))) :
    weightedOldMateLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj RM).toFunctor s g b) =
      -BalancedInduction.tensor J (RM).toFunctor ((J).obj s)
        (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i * D.parity i) ((J).map g)) b :=
  CyclotomicCrossingTensor.oldModuleMate_total_tensor D Sc cutoff i RM s w g b

/-- Append comparison after a given input-module map. The input module is
kept independent so the literal coend dictionaries are fixed before restriction. -/
def weightedAppendSourceLinear
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj T L.toFunctor ((Q).obj w) :=
  weightedAppendComparisonLinear D Sc cutoff N i L w ∘ₗ BalancedInduction.mapComponent J c 0 w

theorem weightedAppendSourceLinear_tensor
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L)
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : R.obj s) :
    weightedAppendSourceLinear D Sc cutoff N i R L c w
      (BalancedInduction.tensor J R.toFunctor s g b) =
      BalancedInduction.tensor T L.toFunctor ((Q).obj s) ((Q).map g) (c.app 0 s b) := by
  have hm := BalancedInduction.mapComponent_tensor J c 0 w s g b
  have hx := hm.trans (congrArg (fun z => BalancedInduction.tensor J
    (weightedRestriction D Sc cutoff N L).toFunctor s z (c.app 0 s b)) (twist_zero g))
  exact (congrArg (weightedAppendComparisonLinear D Sc cutoff N i L w) hx).trans
    (appendWeightedModuleIso_hom_tensor D Sc cutoff N i L s w g (c.app 0 s b))

/-- The old prescribed mate after an input map, with an independent coend source. -/
def weightedOldMatePrecomposeLinear
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj J (RM).toFunctor ((J).obj w) :=
  weightedOldMateLinear D Sc cutoff N i M w ∘ₗ BalancedInduction.mapComponent J c 0 w

theorem weightedOldMatePrecomposeLinear_tensor
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM)
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : R.obj s) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M R c w
      (BalancedInduction.tensor J R.toFunctor s g b) =
      -BalancedInduction.tensor J (RM).toFunctor ((J).obj s)
        (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i * D.parity i) ((J).map g)) (c.app 0 s b) := by
  have hm := BalancedInduction.mapComponent_tensor J c 0 w s g b
  have hx := hm.trans (congrArg (fun z => BalancedInduction.tensor J
    ((BalancedInduction.restriction J).obj RM).toFunctor s z (c.app 0 s b)) (twist_zero g))
  exact (congrArg (weightedOldMateLinear D Sc cutoff N i M w) hx).trans
    (weightedOldMateLinear_tensor D Sc cutoff N i M s w g (c.app 0 s b))

private theorem restrictionInv_comp_zero
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (s : OldCategory D Sc cutoff) (b : R.obj s) :
    (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b = c.app 0 s b := by
  change c.app 0 s b + 0 = c.app 0 s b
  exact add_zero _

/-- The strict append square retains its literal mapped arrow. -/
theorem oldTruncateFunctor_map_append (s w : OldCategory D Sc cutoff) (g : s ⟶ w) :
    (Q).map ((J).map g) = (T).map ((Q).map g) := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff s.word w.word).mkQ_surjective g
  rfl

/-- The ordered mate square after any input map. The independent input
module fixes the literal coend dictionaries before restriction is specialized. -/
theorem weightedAppendMateSquare
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        weightedOldMatePrecomposeLinear D Sc cutoff N i M R c w =
      orderedMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i R ((BalancedInduction.restriction T).obj M)
          (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) w := by
  apply BalancedInduction.hom_ext
  intro s g b
  let c' := c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv
  have ho := weightedOldMatePrecomposeLinear_tensor D Sc cutoff N i M R c s w g b
  have hq := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M ((J).obj s) ((J).obj w)
    (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g)) (c.app 0 s b)
  have hn := map_neg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w))
    (BalancedInduction.tensor J (RM).toFunctor ((J).obj s)
      (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((J).map g)) (c.app 0 s b))
  have hqNeg := congrArg
    (fun z : BalancedInduction.Obj T M.toFunctor ((Q).obj ((J).obj w)) => -z) hq
  have hneg := hn.trans hqNeg
  have hl := (congrArg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w)) ho).trans hneg
  have hs := weightedAppendSourceLinear_tensor D Sc cutoff N i R
    ((BalancedInduction.restriction T).obj M) c' s w g b
  have ht := orderedMateLinear_tensor T (truncatedEqualCross_supernatural D Sc cutoff N i) M
    ((Q).obj s) ((Q).obj w) ((Q).map g) (c'.app 0 s b)
  have hr := (congrArg (orderedMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i)
    M ((Q).obj w)) hs).trans ht
  have ha : (Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g)) =
      truncatedEqualCrossComponent D Sc cutoff N i ((Q).obj s) ≫
        twist k (D.parity i * D.parity i) ((T).map ((Q).map g)) := by
    rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_equalCross, oldTruncateFunctor_map_append]
  have hb := restrictionInv_comp_zero D Sc cutoff N i M R c s b
  have he := congrArg Neg.neg (congrArg₂
    (fun z x => BalancedInduction.tensor T M.toFunctor ((Q).obj ((J).obj s)) z x) ha hb.symm)
  exact hl.trans (he.trans hr.symm)

/-- The selected comparison transports the given old mate with its canonical
restriction comparison. The input map is the identity, with no additional premise. -/
theorem appendWeightedModuleIso_hom_mate (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        weightedOldMatePrecomposeLinear D Sc cutoff N i M
          ((BalancedInduction.restriction J).obj RM) (𝟙 _) w =
      orderedMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M)
          ((𝟙 _) ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) w :=
  weightedAppendMateSquare D Sc cutoff N i M ((BalancedInduction.restriction J).obj RM) (𝟙 _) w

end OddMath.QuiverHecke.ELVOld

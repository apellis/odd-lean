import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixSquares

/-! # Prescribed weighted matrix fields in canonical coordinates

DeformedMatrixComparison (2), (4): each prescribed shifted field commutes
with the selected append chart. Raw field formulas are established before
specializing the input module to the weighted restriction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u

section LinearKernels
variable {k V W X Y : Type u} [CommRing k]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
private theorem unitPlain_reencode (c c₀ : W →ₗ[k] Y) (f : V →ₗ[k] W)
    (g g₀ : V →ₗ[k] Y) (hc : c = c₀) (hg : g₀ = g) (h : c₀ ∘ₗ f = g₀) :
    c ∘ₗ f = g ∘ₗ LinearMap.id := by
  rw [hc, LinearMap.comp_id]
  exact h.trans hg
private theorem capPlain_reencode (d d₀ : V →ₗ[k] X) (f : V →ₗ[k] W) (g : X →ₗ[k] W)
    (hd : d = d₀) (h : g ∘ₗ d₀ = f) : LinearMap.id ∘ₗ f = g ∘ₗ d := by
  rw [hd, LinearMap.id_comp]
  exact h.symm
end LinearKernels

section Endpoints
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s} (hδ : IsSupernatural k p δ)
private theorem unitEndpoint_refl (P : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    endpointUnitDotLinear A hδ P n w (A.obj w) rfl = unitDotLinear A hδ P n w := by
  unfold endpointUnitDotLinear unitDotLinear
  rw [eqToHom_refl, postcompose_id, LinearMap.id_comp]
private theorem mapComponent_identity (P : Superfunctor k C (SVec k)) (w : C) :
    mapComponent A (𝟙 P) 0 w = LinearMap.id := by
  apply hom_ext
  intro s a b
  rw [mapComponent_tensor, twist_zero]
  rfl
end Endpoints

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "J" => append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local instance weightedEntryOldPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory
local instance weightedEntryNewPi : PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

private theorem parity_square (p : ZMod 2) : p * p = p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp only [h, mul_zero, one_mul]

private def oldMateRaw (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    Obj J ((restriction J).obj P).toFunctor w →ₗ[k] Obj J P.toFunctor ((J).obj w) :=
  ((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) P).total w

private theorem oldMate_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((matrixMateComponent D Sc cutoff i P).total w) = oldMateRaw D Sc cutoff i P w := by
  exact congrArg (fun q => ((oldModuleMate D Sc cutoff i).app q P).total w)
    (parity_square (D.parity i)).symm
private theorem oldUnit_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((moduleUnitColumn D Sc cutoff i P n).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldUnitColumn_eq, unitDotColumn_total]
private theorem oldCap_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((moduleCapRow D Sc cutoff i P n).total w) =
      capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldCapRow_eq, capDotRow_total]

private theorem oldUnitEntry_none_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i P m none).total w) =
      oldMateRaw D Sc cutoff i P w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          ((induction J).obj ((restriction J).obj P))).hom.total w) := by
  rw [unitMatrixEntry_none, Superfunctor.comp_total, SVec.toLinearMap_comp, oldMate_total]
private theorem oldUnitEntry_some_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i P m (some r)).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).hom.total w) := by
  change SVec.toLinearMap ((((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).hom ≫
    moduleUnitColumn D Sc cutoff i P r.val).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, oldUnit_total]
private theorem oldCapEntry_none_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i P m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction J).obj ((induction J).obj P))).inv.total w) ∘ₗ oldMateRaw D Sc cutoff i P w := by
  change SVec.toLinearMap ((matrixMateComponent D Sc cutoff i P ≫
    ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction J).obj ((induction J).obj P))).inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, oldMate_total]
private theorem oldCapEntry_some_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i P m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).inv.total w) ∘ₗ
        capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P r.val w := by
  change SVec.toLinearMap ((moduleCapRow D Sc cutoff i P r.val ≫
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, oldCap_total]

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem selectedOldMate_eq (w : OldCategory D Sc cutoff) :
    weightedOldMateLinear D Sc cutoff N i M w = oldMateRaw D Sc cutoff i RM w := rfl
private theorem oldMatePrecompose_identity (w : OldCategory D Sc cutoff) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M ((restriction J).obj RM) (𝟙 _) w =
      weightedOldMateLinear D Sc cutoff N i M w := by
  unfold weightedOldMatePrecomposeLinear
  rw [mapComponent_identity, LinearMap.comp_id]

/-- The selected genuine charts intertwine the prescribed raw mate, without an entry compatibility hypothesis. -/
theorem weightedMatrixCharts_mate (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ oldMateRaw D Sc cutoff i RM w =
      orderedMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M ((Q).obj w) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  have h := appendWeightedModuleIso_hom_mate D Sc cutoff N i M w
  rw [oldMatePrecompose_identity, Category.id_comp] at h
  exact linearSquare_reencode _ _ _ _ _ _ _ _
    (weightedMateTargetLinearEquiv_hom D Sc cutoff N i M w)
    (selectedOldMate_eq D Sc cutoff N i M w).symm
    (endpointMateLinear_refl T (truncatedEqualCross_supernatural D Sc cutoff N i) M ((Q).obj w)).symm
    (weightedMateSourceLinearEquiv_hom D Sc cutoff N i M w) h

/-- Every given raw unit/dot column commutes with the same chosen chart. -/
theorem weightedMatrixCharts_unit (w : OldCategory D Sc cutoff) (n : ℕ) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) RM n w =
      unitDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) ∘ₗ LinearMap.id := by
  exact unitPlain_reencode _ _ _ _ _
    (weightedMateTargetLinearEquiv_hom D Sc cutoff N i M w)
    (unitEndpoint_refl T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w))
    (weightedMateTargetLinear_unitDot D Sc cutoff N i M w n)

/-- Every given raw dot/counit row commutes with the same chosen chart. -/
theorem weightedMatrixCharts_cap (w : OldCategory D Sc cutoff) (n : ℕ) :
    LinearMap.id ∘ₗ capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) RM n w =
      capDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  exact capPlain_reencode _ _ _ _ (weightedMateSourceLinearEquiv_hom D Sc cutoff N i M w)
    (weightedMateSourceLinear_capDot D Sc cutoff N i M w n)

/-- The given first source-shifted field commutes with the canonical EF chart. -/
theorem weightedMatrixCharts_unitEntry_none (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i RM m none).total w) =
      SVec.toLinearMap ((weightedUnitMatrixEntry D Sc cutoff N i M m none).total ((Q).obj w)) ∘ₗ
        (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w none).toLinearMap := by
  have h := weightedMatrixCharts_mate D Sc cutoff N i M w
  have hz := shiftedModuleValueLinearEquiv_source_square
    ((induction J).obj ((restriction J).obj RM)) (induced T ((restriction T).obj M))
    w ((Q).obj w) (weightedMateSourceLinearEquiv D Sc cutoff N i M w) (D.parity i)
  have ho := oldUnitEntry_none_total D Sc cutoff i RM m w
  have hn := inductionUnitMatrixEntry_none_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square (D.parity i)) M m ((Q).obj w)
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- The given first target-shifted field commutes with the canonical FE chart. -/
theorem weightedMatrixCharts_capEntry_none (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedCapFamilyValueEquiv D Sc cutoff N i M m w none).toLinearMap ∘ₗ
        SVec.toLinearMap ((capMatrixEntry D Sc cutoff i RM m none).total w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m none).total ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  have h := weightedMatrixCharts_mate D Sc cutoff N i M w
  have hz := shiftedModuleValueLinearEquiv_target_square
    ((restriction J).obj ((induction J).obj RM)) ((restriction T).obj (induced T M))
    w ((Q).obj w) (weightedMateTargetLinearEquiv D Sc cutoff N i M w) (D.parity i)
  have ho := oldCapEntry_none_total D Sc cutoff i RM m w
  have hn := inductionCapMatrixEntry_none_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square (D.parity i)) M m ((Q).obj w)
  exact linearRow_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every given unit/dot field commutes with the canonical value-coordinate chart. -/
theorem weightedMatrixCharts_unitEntry_some (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i RM m (some r)).total w) =
      SVec.toLinearMap ((weightedUnitMatrixEntry D Sc cutoff N i M m (some r)).total ((Q).obj w)) ∘ₗ
        (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w (some r)).toLinearMap := by
  have h := weightedMatrixCharts_unit D Sc cutoff N i M w r.val
  have hz := shiftedModuleValueLinearEquiv_source_square RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (r.val • D.parity i)
  have ho := oldUnitEntry_some_total D Sc cutoff i RM m r w
  have hn := inductionUnitMatrixEntry_some_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square (D.parity i)) M m r ((Q).obj w)
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every given dot/counit field commutes with the canonical value-coordinate chart. -/
theorem weightedMatrixCharts_capEntry_some (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    (weightedCapFamilyValueEquiv D Sc cutoff N i M m w (some r)).toLinearMap ∘ₗ
        SVec.toLinearMap ((capMatrixEntry D Sc cutoff i RM m (some r)).total w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m (some r)).total ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  have h := weightedMatrixCharts_cap D Sc cutoff N i M w r.val
  have hz := shiftedModuleValueLinearEquiv_target_square RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (r.val • D.parity i)
  have ho := oldCapEntry_some_total D Sc cutoff i RM m r w
  have hn := inductionCapMatrixEntry_some_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square (D.parity i)) M m r ((Q).obj w)
  exact linearRow_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every prescribed unit field, including the crossing-derived slot, commutes with its given chart. -/
theorem weightedMatrixCharts_unitEntry (m : ℕ) (a : Option (Fin m)) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i RM m a).total w) =
      SVec.toLinearMap ((weightedUnitMatrixEntry D Sc cutoff N i M m a).total ((Q).obj w)) ∘ₗ
        (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w a).toLinearMap := by
  cases a with
  | none => exact weightedMatrixCharts_unitEntry_none D Sc cutoff N i M m w
  | some r => exact weightedMatrixCharts_unitEntry_some D Sc cutoff N i M m r w

/-- Every prescribed cap field, including the crossing-derived slot, commutes with its given chart. -/
theorem weightedMatrixCharts_capEntry (m : ℕ) (a : Option (Fin m)) (w : OldCategory D Sc cutoff) :
    (weightedCapFamilyValueEquiv D Sc cutoff N i M m w a).toLinearMap ∘ₗ
        SVec.toLinearMap ((capMatrixEntry D Sc cutoff i RM m a).total w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m a).total ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  cases a with
  | none => exact weightedMatrixCharts_capEntry_none D Sc cutoff N i M m w
  | some r => exact weightedMatrixCharts_capEntry_some D Sc cutoff N i M m r w

end OddMath.QuiverHecke.ELVOld

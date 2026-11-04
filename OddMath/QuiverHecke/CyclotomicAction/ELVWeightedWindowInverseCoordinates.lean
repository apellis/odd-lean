import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedCapInverse
import OddMath.Algebra.FiniteSupermoduleCoordinates

/-! # Window entries of the specified weighted local inverses

BE (1.13)–(1.14): evaluation retains every finite projection or insertion
of the same finite content matrix inverse, with its named parity isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
  CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) (β : Multiset I)
local instance weightedWindowPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local instance weightedWindowOldPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "R" => restriction (contentInclusion D Sc cutoff N β)

/-- The unit local window is the actual inverse's literal `some j` row. -/
theorem weightedContentLocalInverseFrom_window_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (j : Fin (contentUnitCount D cutoff i β))
    (z : ((restriction (T)).obj (induced (T) M)).obj w.obj) :
    ((weightedContentLocalInverseFrom D Sc cutoff N i M β hh).g' j.val).total w z =
      (((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).hom.total w.obj)
        (((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z) (some j)) := by
  classical
  dsimp only [weightedContentLocalInverseFrom, localInverseFromColumns,
    inverseUnitSlot]
  simp only [j.isLt, dite_true]
  dsimp only [inverseCoordinateRow, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.comp_id, Superfunctor.comp_total]
  change (((R).mapIso ((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M)).hom.total w)
      ((projectionHom (fun a => (R).obj (weightedUnitMatrixFamily D Sc cutoff N i M
        (contentUnitCount D cutoff i β) a)) (some j)).total w
        ((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z)) = _
  rw [projectionHom_total_apply]
  rfl

/-- The cap local window is the actual inverse's literal `some j` column. -/
theorem weightedContentLocalInverseTo_window_total
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (j : Fin (contentCapCount D cutoff i β)) (z : M.obj w.obj) :
    ((weightedContentLocalInverseTo D Sc cutoff N i M β hh).g' j.val).total w z =
      (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
        (Pi.single (some j)
          ((((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).inv.total w.obj) z)) := by
  classical
  dsimp only [weightedContentLocalInverseTo, localInverseToRows,
    inverseCapSlot]
  simp only [j.isLt, dite_true]
  dsimp only [inverseCoordinateColumn, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.id_comp, Superfunctor.comp_total]
  change (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
    ((inclusionHom (fun a => (R).obj (weightedCapMatrixFamily D Sc cutoff N i M
        (contentCapCount D cutoff i β) a)) (some j)).total w
      ((((R).mapIso ((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M)).inv.total w) z)) = _
  congr 1
  apply funext
  intro a
  by_cases ha : a = some j
  · subst a
    simp only [inclusionHom_total_self, Pi.single_eq_same]
    rfl
  · rw [inclusionHom_total_ne _ (some j) a (Ne.symm ha)]
    symm
    apply Pi.single_eq_of_ne
    exact ha

local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem moduleIso_apply {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : F.obj w) :
    moduleIsoLinearEquiv e w x = e.hom.total w x := rfl
private theorem moduleIso_symm_apply {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : G.obj w) :
    (moduleIsoLinearEquiv e w).symm x = e.inv.total w x := rfl

/-- Every finite weighted inverse row is retained by the full matrix chart. -/
theorem weightedUnitInverse_window (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (w.word : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    weightedUnitFamilyValueEquiv D Sc cutoff N i M _ w (some j)
      (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some j)) =
    ((weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)) (some j) :=
  congrFun (weightedUnitInverse_coordinates D Sc cutoff N i M w hh z) (some j)

/-- Every finite unit `g'` retains the OLD inverse row in the selected chart. -/
theorem weightedContentUnitWindow_chart (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (w.word : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    ((weightedContentLocalInverseFrom D Sc cutoff N i M (w.word : Multiset I) hh).g' j.val).total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I))
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z) =
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso RM) w
      (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some j)) := by
  have h₀ := weightedContentLocalInverseFrom_window_total D Sc cutoff N i M
    (w.word : Multiset I) hh
    (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) j
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)
  rw [weightedContentUnitInverse_atWord D Sc cutoff N i M w hh] at h₀
  have h₁ := shiftedModuleValueLinearEquiv_hom_coordinate RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (j.val • D.parity i)
    (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some j))
  have h₂ := congrArg
    (((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).hom.total ((Q).obj w))
    (weightedUnitInverse_window D Sc cutoff N i M w hh j z)
  dsimp only [weightedUnitFamilyValueEquiv] at h₂
  simp only [moduleIso_apply]
  exact h₀.trans (h₂.symm.trans h₁)

/-- Every finite cap target insertion retains its prescribed parity chart. -/
theorem weightedCapWindowInput_coordinates (w : OldCategory D Sc cutoff)
    (m : ℕ) (j : Fin m) (z : (RM).obj w) :
    weightedCapMatrixValueEquiv D Sc cutoff N i M m w
      (Pi.single (some j)
        ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
          (j.val • D.parity i)).iso RM) w).symm z)) =
    Pi.single (some j)
      ((((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).inv.total ((Q).obj w)) z) := by
  classical
  funext a
  change weightedCapFamilyValueEquiv D Sc cutoff N i M m w a
    ((Pi.single (some j)
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (j.val • D.parity i)).iso RM) w).symm z) :
      ∀ a, (capMatrixFamily D Sc cutoff i RM m a).obj w) a) = _
  by_cases ha : a = some j
  · subst a
    simp only [Pi.single_eq_same, moduleIso_symm_apply]
    dsimp only [weightedCapFamilyValueEquiv]
    exact shiftedModuleValueLinearEquiv_inv_coordinate RM M w ((Q).obj w)
      (LinearEquiv.refl k _) (j.val • D.parity i) z
  · simp only [Pi.single_eq_of_ne ha, map_zero]

/-- Every finite cap `g'` retains the OLD inverse column in the selected chart. -/
theorem weightedContentCapWindow_chart (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (j : Fin (contentCapCount D cutoff i (w.word : Multiset I))) (z : (RM).obj w) :
    ((weightedContentLocalInverseTo D Sc cutoff N i M (w.word : Multiset I) hh).g' j.val).total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) z =
    weightedMateSourceLinearEquiv D Sc cutoff N i M w
      ((moduleCapMatrixIso D Sc cutoff RM i w hh).inv
        (Pi.single (some j)
          ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
            (j.val • D.parity i)).iso RM) w).symm z))) := by
  have h₀ := weightedContentLocalInverseTo_window_total D Sc cutoff N i M
    (w.word : Multiset I) hh
    (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) j z
  rw [weightedContentCapInverse_atWord D Sc cutoff N i M w hh] at h₀
  have h₁ := congrArg (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).inv
    (weightedCapWindowInput_coordinates D Sc cutoff N i M w
      (contentCapCount D cutoff i (w.word : Multiset I)) j z)
  have h₂ := weightedCapInverse_coordinates D Sc cutoff N i M w hh
    (Pi.single (some j)
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (j.val • D.parity i)).iso RM) w).symm z))
  exact h₀.trans (h₁.symm.trans h₂.symm)

end OddMath.QuiverHecke.ELVOld

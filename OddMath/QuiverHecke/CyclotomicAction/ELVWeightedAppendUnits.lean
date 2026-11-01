import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientTensors

/-! # Unit generators of the weighted append comparison
SwappedVacuumCoordinates §6 uses the chosen old-to-truncated comparison.
We compute its five canonical maps on coend units before extending to tensors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

/-- The last comparison leg uses the literal quotient-induction counit. -/
theorem quotientCounit_moduleMap_unit_tensor (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (s : OldCategory D Sc cutoff) (w : TruncatedCategory D Sc cutoff N)
    (g : (truncatedAppend D Sc cutoff N [i]).obj (Q.obj s) ⟶ w)
    (b : M.obj (Q.obj s)) :
    ((BalancedInduction.induction (truncatedAppend D Sc cutoff N [i])).map
      (quotientInductionCounitIso D Sc cutoff N M).hom).total w
        (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i])
          (BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M)).toFunctor
          (Q.obj s) g
          (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b)) =
      BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor (Q.obj s) g b := by
  have hf : (quotientInductionCounitIso D Sc cutoff N M).hom ∈ parity (R := k) _ _ 0 := by
    rw [quotientInductionCounitIso_hom]
    exact BalancedInduction.adjunctionCounit_mem Q M
  have hm : (BalancedInduction.induction (truncatedAppend D Sc cutoff N [i])).map
      (quotientInductionCounitIso D Sc cutoff N M).hom =
      BalancedInduction.moduleMap (truncatedAppend D Sc cutoff N [i])
        (quotientInductionCounitIso D Sc cutoff N M).hom := rfl
  rw [hm, BalancedInduction.moduleMap_total_tensor_even _ _ hf]
  have hb : (quotientInductionCounitIso D Sc cutoff N M).hom.app 0 (Q.obj s)
      (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b) = b := by
    change BalancedInduction.counit Q M.toFunctor (Q.obj s)
      (BalancedInduction.unit Q (Q ⋙ M.toFunctor) s b) = b
    exact LinearMap.congr_fun (BalancedInduction.counit_unit Q M.toFunctor s) b
  exact congrArg (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor
    (Q.obj s) g) hb

variable (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "R" => weightedRestriction D Sc cutoff N M
local notation "L" => BalancedInduction.induced J R
local notation "hL" => induced_killsWeightedCoefficients D Sc cutoff N i R
  (weightedRestriction_kills D Sc cutoff N M)

private theorem weightedAppendSquare_unit (s : OldCategory D Sc cutoff) (b : M.obj (Q.obj s)) :
    (BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
      (oldAppend_truncate D Sc cutoff N i) R).hom.total (Q.obj (J.obj s))
      (BalancedInduction.unit (J ⋙ Q) R.toFunctor s b) =
      BalancedInduction.unit (Q ⋙ T) R.toFunctor s b := by
  have h := BalancedInduction.inducedIsoOfFunctorEq_tensor (J ⋙ Q) (Q ⋙ T)
    (oldAppend_truncate D Sc cutoff N i) R s (Q.obj (J.obj s)) (𝟙 _) b
  refine h.trans ?_
  have hi : eqToHom (congrArg
      (fun F : OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N => F.obj s)
      (oldAppend_truncate D Sc cutoff N i)).symm ≫ 𝟙 (Q.obj (J.obj s)) =
        𝟙 (T.obj (Q.obj s)) := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  exact congrArg (fun z : (Q ⋙ T).obj s ⟶ (Q ⋙ T).obj s =>
    BalancedInduction.tensor (Q ⋙ T) R.toFunctor s z b) hi

/-- The selected comparison retains the source vector on a coend unit. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj (Q.obj s)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total (Q.obj (J.obj s))
      (BalancedInduction.unit J R.toFunctor s b) =
      BalancedInduction.unit T M.toFunctor (Q.obj s) b := by
  have he : (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (quotientInducedWeightedModuleIso D Sc cutoff N L hL).inv ≫
        (BalancedInduction.inductionComp J Q).hom.app R ≫
          (BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
            (oldAppend_truncate D Sc cutoff N i) R).hom ≫
            (BalancedInduction.inductionComp Q T).inv.app R ≫
              BalancedInduction.moduleMap T
                (quotientInductionCounitIso D Sc cutoff N M).hom := rfl
  rw [he]
  simp only [Superfunctor.comp_total, SVec.comp_apply]
  rw [quotientInducedWeightedModuleIso_inv_tensor,
    BalancedInduction.inductionComp_hom_total_unit, weightedAppendSquare_unit,
    BalancedInduction.inductionComp_inv_total_unit]
  exact quotientCounit_moduleMap_unit_tensor D Sc cutoff N i M s (T.obj (Q.obj s)) (𝟙 _) b

end OddMath.QuiverHecke.ELVOld

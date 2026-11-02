import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendParity

/-! # Literal tensor generators of weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
the selected old/truncated comparison
preserves the input vector and sends every old coend arrow to its literal
quotient. No homogeneity restriction is imposed on either tensor factor.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "F" => BalancedInduction.induced J RM
local notation "hF" => induced_killsWeightedCoefficients D Sc cutoff N i RM
  (weightedRestriction_kills D Sc cutoff N M)

private def appendQuotientCounit : (BalancedInduction.induction Q).obj RM ⟶ M :=
  (quotientInductionCounitIso D Sc cutoff N M).hom

private theorem appendQuotientCounit_mem :
    appendQuotientCounit D Sc cutoff N M ∈ parity (R := k) _ _ 0 :=
  quotientInductionCounitIso_hom_mem D Sc cutoff N M

private def appendSquareMap : BalancedInduction.induced Q F ⟶ BalancedInduction.induced T M :=
  BalancedInduction.squareComparison J Q Q T (oldAppend_truncate D Sc cutoff N i) RM M
    (appendQuotientCounit D Sc cutoff N M)

private def appendQuotientInverse :
    weightedInducedModule D Sc cutoff N i RM (weightedRestriction_kills D Sc cutoff N M) ⟶
      BalancedInduction.induced Q F :=
  (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv

private theorem appendQuotientInverse_tensor
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : M.obj ((Q).obj s)) :
    (appendQuotientInverse D Sc cutoff N i M).total ((Q).obj w)
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b) :=
  quotientInducedWeightedModuleIso_inv_tensor D Sc cutoff N F hF ((Q).obj w)
    (BalancedInduction.tensor J (RM).toFunctor s g b)

private theorem appendWeightedModuleIso_hom_factor :
    (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (appendQuotientInverse D Sc cutoff N i M) ≫
        appendSquareMap D Sc cutoff N i M := by
  unfold appendQuotientInverse appendSquareMap
  rw [BalancedInduction.squareComparison_eq]
  rfl

private theorem appendSquareMap_total_tensor
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : M.obj ((Q).obj s)) :
    (appendSquareMap D Sc cutoff N i M).total ((Q).obj w)
      (BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b)) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s)
        (eqToHom (congrArg
          (fun H : OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N => H.obj s)
          (oldAppend_truncate D Sc cutoff N i)).symm ≫ (Q).map g)
        ((appendQuotientCounit D Sc cutoff N M).app 0 ((Q).obj s)
          (BalancedInduction.unit Q (RM).toFunctor s b)) := by
  have hs := BalancedInduction.squareComparison_total_tensor J Q Q T
    (oldAppend_truncate D Sc cutoff N i) RM M
    (appendQuotientCounit D Sc cutoff N M)
    (appendQuotientCounit_mem D Sc cutoff N M) s w g b
  set_option backward.dsimp.instances true in
    dsimp only [appendSquareMap, BalancedInduction.induction] at hs ⊢
  exact hs

/-- The chosen five-isomorphism comparison sends the old tensor to the
truncated tensor with exactly the quotient arrow and unchanged vector. -/
theorem appendWeightedModuleIso_hom_tensor
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w)
    (b : M.obj ((Q).obj s)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj w)
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
  rw [appendWeightedModuleIso_hom_factor, Superfunctor.comp_total, SVec.comp_apply,
    appendQuotientInverse_tensor]
  refine (appendSquareMap_total_tensor D Sc cutoff N i M s w g b).trans ?_
  have hi : eqToHom (congrArg
      (fun H : OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N => H.obj s)
      (oldAppend_truncate D Sc cutoff N i)).symm ≫ (Q).map g = (Q).map g := by
    change 𝟙 _ ≫ (Q).map g = (Q).map g
    exact Category.id_comp _
  have hb : (appendQuotientCounit D Sc cutoff N M).app 0 ((Q).obj s)
      (BalancedInduction.unit Q (RM).toFunctor s b) = b := by
    change BalancedInduction.counit Q M.toFunctor ((Q).obj s)
      (BalancedInduction.unit Q (Q ⋙ M.toFunctor) s b) = b
    exact LinearMap.congr_fun (BalancedInduction.counit_unit Q M.toFunctor s) b
  rw [hi, hb]

/-- In particular the selected comparison sends the old unit to the
truncated unit, with the same vector. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj ((J).obj s))
      (BalancedInduction.unit J (RM).toFunctor s b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
  have hs := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M s ((J).obj s) (𝟙 _) b
  refine hs.trans ?_
  exact congrArg (fun z : (T).obj ((Q).obj s) ⟶ (T).obj ((Q).obj s) =>
    BalancedInduction.tensor T M.toFunctor ((Q).obj s) z b) ((Q).map_id ((J).obj s))

end OddMath.QuiverHecke.ELVOld

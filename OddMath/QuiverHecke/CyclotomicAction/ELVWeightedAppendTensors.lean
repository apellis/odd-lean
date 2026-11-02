import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendParity

/-! # Literal tensor generators of weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
the selected old/truncated comparison preserves the input vector and sends
every old coend arrow to its literal quotient. No homogeneity restriction
is imposed on either tensor factor.
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

local notation "S" => BalancedInduction.squareLinear J Q Q T
  (oldAppend_truncate D Sc cutoff N i) RM M (appendQuotientCounit D Sc cutoff N M)

private theorem appendWeightedModuleIso_hom_factor :
    (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv ≫
        BalancedInduction.squareComparison J Q Q T (oldAppend_truncate D Sc cutoff N i)
          RM M (quotientInductionCounitIso D Sc cutoff N M).hom := by
  rw [BalancedInduction.squareComparison_eq]
  rfl

/-- The chosen comparison on the literal old and truncated coends.
The endpoint module instances are fixed before generator evaluation. -/
def weightedAppendComparisonLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj T M.toFunctor ((Q).obj w) :=
  (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj w)

private def appendQuotientInverseLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj Q (F).toFunctor ((Q).obj w) :=
  (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv.total ((Q).obj w)

private theorem weightedAppendComparisonLinear_factor (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M w =
      S ((Q).obj w) ∘ₗ appendQuotientInverseLinear D Sc cutoff N i M w := by
  exact (BalancedInduction.total_linear_congr
    (appendWeightedModuleIso_hom_factor D Sc cutoff N i M) ((Q).obj w)).trans
      (BalancedInduction.composition_total_linear _ _ ((Q).obj w))

/-- The selected five-isomorphism comparison sends the old tensor to the
truncated tensor with exactly the quotient arrow and unchanged vector. -/
theorem appendWeightedModuleIso_hom_tensor
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w)
    (b : M.obj ((Q).obj s)) :
    weightedAppendComparisonLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
  have h₁ : appendQuotientInverseLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b) :=
    quotientInducedWeightedModuleIso_inv_tensor D Sc cutoff N F hF ((Q).obj w)
      (BalancedInduction.tensor J (RM).toFunctor s g b)
  have h₂ := BalancedInduction.squareLinear_tensor J Q Q T
    (oldAppend_truncate D Sc cutoff N i) RM M (appendQuotientCounit D Sc cutoff N M)
    (quotientInductionCounitIso_hom_mem D Sc cutoff N M) s w g b
  have hs : S ((Q).obj w)
      (BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b)) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
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
    exact h₂.trans (congrArg₂
      (fun z x => BalancedInduction.tensor T M.toFunctor ((Q).obj s) z x) hi hb)
  rw [weightedAppendComparisonLinear_factor, LinearMap.comp_apply]
  exact (congrArg (S ((Q).obj w)) h₁).trans hs

/-- The same selected comparison preserves the literal coend units. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj s)
      (BalancedInduction.unit J (RM).toFunctor s b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
  have h := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M s ((J).obj s) (𝟙 _) b
  have hin := congrArg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj s))
    (BalancedInduction.unit_apply J (RM).toFunctor s b)
  have hout := BalancedInduction.unit_apply T M.toFunctor ((Q).obj s) b
  exact hin.trans ((h.trans (congrArg
    (fun z => BalancedInduction.tensor T M.toFunctor ((Q).obj s) z b)
    ((Q).map_id ((J).obj s)))).trans hout.symm)

end OddMath.QuiverHecke.ELVOld

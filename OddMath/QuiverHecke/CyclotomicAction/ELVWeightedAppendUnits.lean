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
    (g : (truncatedAppend D Sc cutoff N [i]).obj ((Q).obj s) ⟶ w)
    (b : M.obj ((Q).obj s)) :
    ((BalancedInduction.induction (truncatedAppend D Sc cutoff N [i])).map
      (quotientInductionCounitIso D Sc cutoff N M).hom).total w
        (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i])
          (BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M)).toFunctor
          ((Q).obj s) g
          (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b)) =
      BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor ((Q).obj s) g b := by
  have hf : (quotientInductionCounitIso D Sc cutoff N M).hom ∈ parity (R := k) _ _ 0 := by
    rw [quotientInductionCounitIso_hom]
    exact BalancedInduction.adjunctionCounit_mem Q M
  have hm : (BalancedInduction.induction (truncatedAppend D Sc cutoff N [i])).map
      (quotientInductionCounitIso D Sc cutoff N M).hom =
      BalancedInduction.moduleMap (truncatedAppend D Sc cutoff N [i])
        (quotientInductionCounitIso D Sc cutoff N M).hom := rfl
  rw [hm]
  refine (BalancedInduction.moduleMap_total_tensor_even
    (truncatedAppend D Sc cutoff N [i])
    (quotientInductionCounitIso D Sc cutoff N M).hom hf w ((Q).obj s) g
    (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b)).trans ?_
  have hb : (quotientInductionCounitIso D Sc cutoff N M).hom.app 0 ((Q).obj s)
      (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b) = b := by
    change BalancedInduction.counit Q M.toFunctor ((Q).obj s)
      (BalancedInduction.unit Q (Q ⋙ M.toFunctor) s b) = b
    exact LinearMap.congr_fun (BalancedInduction.counit_unit Q M.toFunctor s) b
  exact congrArg (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor
    ((Q).obj s) g) hb

variable (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "R" => weightedRestriction D Sc cutoff N M
local notation "L" => BalancedInduction.induced J R
local notation "hL" => induced_killsWeightedCoefficients D Sc cutoff N i R
  (weightedRestriction_kills D Sc cutoff N M)

private theorem weightedAppendSquare_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
      (oldAppend_truncate D Sc cutoff N i) R).hom.total ((Q).obj ((J).obj s))
      (BalancedInduction.unit (J ⋙ Q) (R).toFunctor s b) =
      BalancedInduction.unit (Q ⋙ T) (R).toFunctor s b := by
  have h := BalancedInduction.inducedIsoOfFunctorEq_tensor (J ⋙ Q) (Q ⋙ T)
    (oldAppend_truncate D Sc cutoff N i) R s ((Q).obj ((J).obj s)) (𝟙 _) b
  refine h.trans ?_
  have hi : eqToHom (congrArg
      (fun F : OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N => F.obj s)
      (oldAppend_truncate D Sc cutoff N i)).symm ≫ 𝟙 ((Q).obj ((J).obj s)) =
        𝟙 ((T).obj ((Q).obj s)) := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  exact congrArg (fun z : (Q ⋙ T).obj s ⟶ (Q ⋙ T).obj s =>
    BalancedInduction.tensor (Q ⋙ T) (R).toFunctor s z b) hi

/-- The selected comparison retains the source vector on a coend unit. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj ((J).obj s))
      (BalancedInduction.unit J (R).toFunctor s b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
  let w := (Q).obj ((J).obj s)
  let F₀ := weightedModule D Sc cutoff N L hL
  let F₁ := BalancedInduction.induced Q L
  let F₂ := BalancedInduction.induced (J ⋙ Q) R
  let F₃ := BalancedInduction.induced (Q ⋙ T) R
  let F₄ := BalancedInduction.induced T (BalancedInduction.induced Q R)
  let F₅ := BalancedInduction.induced T M
  let f₁ : F₀ ⟶ F₁ := (quotientInducedWeightedModuleIso D Sc cutoff N L hL).inv
  let f₂ : F₁ ⟶ F₂ := (BalancedInduction.inductionComp J Q).hom.app R
  let f₃ : F₂ ⟶ F₃ := (BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
    (oldAppend_truncate D Sc cutoff N i) R).hom
  let f₄ : F₃ ⟶ F₄ := (BalancedInduction.inductionComp Q T).inv.app R
  let f₅ : F₄ ⟶ F₅ := BalancedInduction.moduleMap T
    (quotientInductionCounitIso D Sc cutoff N M).hom
  let x₀ : F₀.obj w := BalancedInduction.unit J (R).toFunctor s b
  have he : (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (show F₀ ⟶ F₅ from f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅) := by
    as_aux_lemma => rfl
  have h₁ : f₁.total w x₀ = BalancedInduction.unit Q (L).toFunctor ((J).obj s) x₀ := by
    exact (quotientInducedWeightedModuleIso_inv_tensor D Sc cutoff N L hL w x₀).trans
      (BalancedInduction.unit_apply Q (L).toFunctor ((J).obj s) x₀).symm
  have h₂ : f₂.total w (BalancedInduction.unit Q (L).toFunctor ((J).obj s) x₀) =
      BalancedInduction.unit (J ⋙ Q) (R).toFunctor s b :=
    BalancedInduction.inductionComp_hom_total_unit J Q R s b
  have h₃ : f₃.total w (BalancedInduction.unit (J ⋙ Q) (R).toFunctor s b) =
      BalancedInduction.unit (Q ⋙ T) (R).toFunctor s b :=
    weightedAppendSquare_unit D Sc cutoff N i M s b
  have h₄ : f₄.total w (BalancedInduction.unit (Q ⋙ T) (R).toFunctor s b) =
      BalancedInduction.unit T (BalancedInduction.induced Q R).toFunctor ((Q).obj s)
        (BalancedInduction.unit Q (R).toFunctor s b) :=
    BalancedInduction.inductionComp_inv_total_unit Q T R s b
  have h₅ : f₅.total w
      (BalancedInduction.unit T (BalancedInduction.induced Q R).toFunctor ((Q).obj s)
        (BalancedInduction.unit Q (R).toFunctor s b)) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
    simpa only [BalancedInduction.unit_apply] using
      quotientCounit_moduleMap_unit_tensor D Sc cutoff N i M s ((T).obj ((Q).obj s)) (𝟙 _) b
  exact (congrArg (fun f : F₀ ⟶ F₅ => f.total w x₀) he).trans
    (BalancedInduction.composition_total_apply_of_steps f₁ f₂ f₃ f₄ f₅ w
      x₀ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅)

end OddMath.QuiverHecke.ELVOld

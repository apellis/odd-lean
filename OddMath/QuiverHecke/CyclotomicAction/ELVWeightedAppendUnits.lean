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

namespace WeightedAppendUnits

private abbrev sourceModule := weightedModule D Sc cutoff N L hL
private abbrev quotientModule := (BalancedInduction.induction Q).obj ((BalancedInduction.induction J).obj R)
private abbrev compositeModule := (BalancedInduction.induction (J ⋙ Q)).obj R
private abbrev squareModule := (BalancedInduction.induction (Q ⋙ T)).obj R
private abbrev iteratedModule := (BalancedInduction.induction T).obj ((BalancedInduction.induction Q).obj R)
private abbrev targetModule := (BalancedInduction.induction T).obj M
private abbrev targetObject (s : OldCategory D Sc cutoff) := (Q).obj ((J).obj s)

local notation "S₀" => sourceModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)
local notation "S₁" => quotientModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)
local notation "S₂" => compositeModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)
local notation "S₃" => squareModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)
local notation "S₄" => iteratedModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)
local notation "S₅" => targetModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)
local notation "w" => targetObject (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i)

private def quotientInverse : S₀ ⟶ S₁ :=
  (quotientInducedWeightedModuleIso D Sc cutoff N L hL).inv
private def flatten : S₁ ⟶ S₂ := (BalancedInduction.inductionComp J Q).hom.app R
private def square : S₂ ⟶ S₃ :=
  (BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
    (oldAppend_truncate D Sc cutoff N i) R).hom
private def unflatten : S₃ ⟶ S₄ := (BalancedInduction.inductionComp Q T).inv.app R
private def counit : S₄ ⟶ S₅ :=
  (BalancedInduction.induction T).map (quotientInductionCounitIso D Sc cutoff N M).hom

private def restrictionVector (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (R).obj s := b
local notation "rvec" => restrictionVector (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (M := M)

private def sourceUnit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) : (S₀).obj (w s) :=
  BalancedInduction.unit J (R).toFunctor s (rvec s b)
private def quotientUnit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) : (S₁).obj (w s) :=
  BalancedInduction.unit Q (L).toFunctor ((J).obj s) (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)
private def compositeUnit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) : (S₂).obj (w s) :=
  BalancedInduction.unit (J ⋙ Q) (R).toFunctor s (rvec s b)
private def squareUnit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) : (S₃).obj (w s) :=
  BalancedInduction.unit (Q ⋙ T) (R).toFunctor s (rvec s b)
private def iteratedUnit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) : (S₄).obj (w s) :=
  BalancedInduction.unit T (BalancedInduction.induced Q R).toFunctor ((Q).obj s)
    (BalancedInduction.unit Q (R).toFunctor s (rvec s b))
private def targetUnit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) : (S₅).obj (w s) :=
  BalancedInduction.unit T M.toFunctor ((Q).obj s) b

private theorem quotientInverse_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (quotientInverse (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)).total (w s) (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) =
      quotientUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b :=
  (quotientInducedWeightedModuleIso_inv_tensor D Sc cutoff N L hL (w s)
    (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)).trans
    (BalancedInduction.unit_apply Q (L).toFunctor ((J).obj s)
      (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)).symm

private theorem flatten_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (flatten (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)).total (w s) (quotientUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) =
      compositeUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b :=
  by
    have h := BalancedInduction.inductionComp_hom_total_unit J Q R s (rvec s b)
    set_option backward.dsimp.instances true in
      dsimp only [BalancedInduction.induction] at h
    set_option backward.dsimp.instances true in
      dsimp only [flatten, quotientUnit, sourceUnit, compositeUnit, sourceModule,
        quotientModule, compositeModule, targetObject, BalancedInduction.induction]
    exact h

private theorem square_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (square (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)).total (w s) (compositeUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) =
      squareUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b :=
  weightedAppendSquare_unit D Sc cutoff N i M s b

private theorem unflatten_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (unflatten (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)).total (w s) (squareUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) =
      iteratedUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b :=
  by
    have h := BalancedInduction.inductionComp_inv_total_tensor Q T R s (w s) (𝟙 _) (rvec s b)
    set_option backward.dsimp.instances true in
      dsimp only [BalancedInduction.induction] at h
    set_option backward.dsimp.instances true in
      dsimp only [unflatten, squareUnit, iteratedUnit, squareModule, iteratedModule,
        targetObject, BalancedInduction.induction]
    simp only [BalancedInduction.unit_apply]
    set_option backward.dsimp.instances true in
      dsimp only [squareModule, iteratedModule, targetObject, BalancedInduction.induction] at h ⊢
    exact h

private theorem counit_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (counit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)).total (w s) (iteratedUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) =
      targetUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b := by
  simpa only [counit, iteratedUnit, targetUnit, restrictionVector, iteratedModule, targetModule, targetObject, BalancedInduction.induction, BalancedInduction.unit_apply] using
    quotientCounit_moduleMap_unit_tensor D Sc cutoff N i M s (w s) (𝟙 _) b

private theorem comparison_hom :
    (appendWeightedModuleIso D Sc cutoff N i M).hom =
      quotientInverse (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) ≫ flatten (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) ≫
        square (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) ≫ unflatten (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) ≫ counit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) := rfl

private theorem comparison_unit (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total (w s)
      (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) = targetUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b := by
  exact (congrArg (fun f : sourceModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) ⟶ targetModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) =>
    f.total (targetObject (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) s) (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b))
      (comparison_hom (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M))).trans
    (BalancedInduction.composition_total_apply_of_steps
      (k := k) (C := TruncatedCategory D Sc cutoff N)
      (F₀ := sourceModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)) (F₁ := quotientModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M))
      (F₂ := compositeModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)) (F₃ := squareModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M))
      (F₄ := iteratedModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)) (F₅ := targetModule (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M))
      (quotientInverse (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)) (flatten (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M))
      (square (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)) (unflatten (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M)) (counit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M))
      (targetObject (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) s)
      (sourceUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) (quotientUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)
      (compositeUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) (squareUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)
      (iteratedUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) (targetUnit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)
      (quotientInverse_unit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) (flatten_unit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)
      (square_unit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b) (unflatten_unit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b)
      (counit_unit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b))


end WeightedAppendUnits

open WeightedAppendUnits in
/-- The selected comparison retains the source vector on a coend unit. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj ((J).obj s))
      (BalancedInduction.unit J (R).toFunctor s b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
  simpa only [sourceUnit, targetUnit, restrictionVector, sourceModule, targetModule, targetObject, BalancedInduction.induction] using
    comparison_unit (D := D) (Sc := Sc) (cutoff := cutoff) (N := N) (i := i) (M := M) s b

end OddMath.QuiverHecke.ELVOld

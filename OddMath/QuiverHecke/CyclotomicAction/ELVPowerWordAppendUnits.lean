import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentCyclicity
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentDot

/-! # Selected word append comparison on cyclic unit tensors

SwappedVacuumCoordinates §4: compute the independently chosen comparison
on a regular coefficient unit and an arbitrary full old-arrow tail. Together
with proved cyclicity this identifies whole chosen crossing maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordAppendUnits
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem map_even_tensor {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (s : C) (w : B) (g : J.obj s ⟶ w) (b : M.obj s) :
    ((BalancedInduction.induction J).map f).total w (BalancedInduction.tensor J M.toFunctor s g b) =
      BalancedInduction.tensor J P.toFunctor s g (f.total s b) := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0)
  change (BalancedInduction.moduleMap J f).total w _ = _
  rw [BalancedInduction.moduleMap_total_tensor, hz]
  simp only [SuperNatTrans.total, hz, add_zero]
  change BalancedInduction.tensor J P.toFunctor s g (f.app 0 s b) +
    BalancedInduction.tensor J P.toFunctor s (twist k 1 g) 0 = _
  rw [BalancedInduction.tensor_zero_right, add_zero]

private theorem mapped_tensor_steps {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M P : Superfunctor k C (SVec k)} {N : Superfunctor k B (SVec k)}
    (e : M ≅ P) (f : BalancedInduction.induced J P ≅ N)
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (s : C) (w : B) (g : J.obj s ⟶ w) (b : M.obj s) (c : P.obj s) (z : N.obj w)
    (hb : e.hom.total s b = c)
    (hc : f.hom.total w (BalancedInduction.tensor J P.toFunctor s g c) = z) :
    (((BalancedInduction.induction J).mapIso e ≪≫ f).hom.total w)
      (BalancedInduction.tensor J M.toFunctor s g b) = z := by
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total, SVec.comp_apply]
  have hm := map_even_tensor J e.hom he s w g b
  exact (congrArg (fun x => f.hom.total w x) hm).trans
    ((congrArg (fun x => f.hom.total w (BalancedInduction.tensor J P.toFunctor s g x)) hb).trans hc)

private theorem inverse_tensor_steps {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M P N : Superfunctor k C (SVec k)} (e : M ≅ P) (f : M ≅ N)
    (w : C) (b : M.obj w) (c : P.obj w) (z : N.obj w)
    (he : e.hom.total w b = c) (hf : f.hom.total w b = z) :
    ((e.symm ≪≫ f).hom.total w) c = z := by
  rw [← he, Iso.trans_hom, Iso.symm_hom, Superfunctor.comp_total]
  exact (congrArg (fun x => f.hom.total w x) ((moduleIsoLinearEquiv e w).symm_apply_apply b)).trans hf

omit [Fintype I] in
private theorem restriction_iso_apply (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (w : OldCategory D Sc cutoff) (b : M.obj w) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).hom.total w b = b := by
  change b + 0 = b
  exact add_zero _

omit [Fintype I] in
private theorem descent_iso_apply (N : ℕ)
    (M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (hP : KillsWeightedCoefficients D Sc cutoff N P)
    (e : M ≅ P) (w : OldCategory D Sc cutoff) (b : M.obj w) :
    (weightedModuleIso D Sc cutoff N M P hM hP e).hom.total
      ((oldTruncateFunctor D Sc cutoff N).obj w) b = e.hom.total w b := rfl

private def oldComparison (ν : List I) (i : I) :
    BalancedInduction.induced (append D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≅ powerWordModule D Sc cutoff L (ν ++ [i]) :=
  (BalancedInduction.induction (append D Sc cutoff i)).mapIso
    (weightedRestrictionModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)) ≪≫
    powerWordAppendIso D Sc cutoff L ν i

private theorem induced_carrier_eq {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (w : B) :
    ((BalancedInduction.induced J M).obj w).carrier =
      BalancedInduction.Obj J M.toFunctor w := rfl

omit [Fintype I] in
private theorem generator_tensor (ν : List I) (w : OldCategory D Sc cutoff)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ w) :
    powerWordGenerator D Sc cutoff L ν w g =
      BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) g
        (1 : CoefficientPowerQuotient (k := k) D cutoff L) := rfl

omit [Fintype I] in
private theorem unit_tensor (ν : List I) :
    PowerWordYoneda.unitVector D Sc cutoff L ν =
      BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) (𝟙 _)
        (1 : CoefficientPowerQuotient (k := k) D cutoff L) := rfl

omit [Fintype I] in
set_option backward.dsimp.instances true in
private theorem oldAppend_tensor_unit (ν : List I) (i : I) (w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ w) :
    (powerWordAppendIso D Sc cutoff L ν i).hom.total w
      (BalancedInduction.tensor (append D Sc cutoff i) (powerWordModule D Sc cutoff L ν).toFunctor
        (OldCategory.mk ν) g (PowerWordYoneda.unitVector D Sc cutoff L ν)) =
      powerWordGenerator D Sc cutoff L (ν ++ [i]) w g := by
  have ho := PowerWordAppend.appendLinear_tensor D Sc cutoff L ν i (OldCategory.mk ν) w g (𝟙 _)
    (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  erw [(append D Sc cutoff i).map_id, Category.id_comp] at ho
  rw [unit_tensor, generator_tensor]
  dsimp only [powerWordModule, PowerWordAppend.appendLinear, BalancedInduction.induction] at ho ⊢
  convert ho using 1
  · exact induced_carrier_eq (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L) w
  · apply congrArg ((powerWordAppendIso D Sc cutoff L ν i).hom.total w)
    apply congrArg (fun b => BalancedInduction.tensor (append D Sc cutoff i)
      (powerWordModule D Sc cutoff L ν).toFunctor (OldCategory.mk ν) g b)
    rfl

set_option backward.dsimp.instances true in
private theorem oldComparison_tensor_unit (ν : List I) (i : I) (w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ w) :
    (oldComparison D Sc cutoff L ν i).hom.total w
      (BalancedInduction.tensor (append D Sc cutoff i)
        (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
          (PowerWordContent.weightedWord D Sc cutoff L ν)).toFunctor (OldCategory.mk ν) g
        (PowerWordYoneda.unitVector D Sc cutoff L ν)) =
    powerWordGenerator D Sc cutoff L (ν ++ [i]) w g := by
  unfold oldComparison
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total, SVec.comp_apply]
  have hm := map_even_tensor (append D Sc cutoff i)
    (weightedRestrictionModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)).hom
    (weightedRestrictionModuleIso_hom_mem D Sc cutoff _ _ _)
    (OldCategory.mk ν) w g (PowerWordYoneda.unitVector D Sc cutoff L ν)
  have hu := restriction_iso_apply D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)
    (OldCategory.mk ν) (PowerWordYoneda.unitVector D Sc cutoff L ν)
  rw [hu] at hm
  dsimp only [PowerWordContent.weightedWord] at hm ⊢
  dsimp only [BalancedInduction.induction] at hm ⊢
  rw [hm]
  exact oldAppend_tensor_unit D Sc cutoff L ν i w g

private def descendedComparison (ν : List I) (i : I) :
    weightedInducedModule D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν))
      (weightedRestriction_kills D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≅
      PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]) :=
  let N := PowerWordContent.powerBound D cutoff L
  let M := PowerWordContent.weightedWord D Sc cutoff L ν
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced (append D Sc cutoff i) R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R (weightedRestriction_kills D Sc cutoff N M)
  weightedModuleIso D Sc cutoff N F (powerWordModule D Sc cutoff L (ν ++ [i])) hF
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i])) (oldComparison D Sc cutoff L ν i)

private theorem weightedAppendIso_eq (ν : List I) (i : I) :
    PowerWordContent.weightedAppendIso D Sc cutoff L ν i =
      (appendWeightedModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
        (PowerWordContent.weightedWord D Sc cutoff L ν)).symm ≪≫
          descendedComparison D Sc cutoff L ν i := rfl

set_option backward.dsimp.instances true in
/-- Arbitrary full old-arrow tail, including its coefficients, with the
actual regular coefficient unit in the chosen truncated induction. -/
theorem weighted_append_tensor_unit (ν : List I) (i : I) (w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ w) :
    (PowerWordContent.weightedAppendIso D Sc cutoff L ν i).hom.total
      ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj w)
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
        (PowerWordContent.weightedWord D Sc cutoff L ν).toFunctor
        ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj (OldCategory.mk ν))
        ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map
          (X := (append D Sc cutoff i).obj (OldCategory.mk ν)) (Y := w) g)
        (PowerWordYoneda.unitVector D Sc cutoff L ν)) =
    powerWordGenerator D Sc cutoff L (ν ++ [i]) w g := by
  have he := appendWeightedModuleIso_hom_tensor D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
    (PowerWordContent.weightedWord D Sc cutoff L ν) (OldCategory.mk ν) w g
    (PowerWordYoneda.unitVector D Sc cutoff L ν)
  dsimp only [weightedAppendComparisonLinear] at he
  have hf := descent_iso_apply D Sc cutoff (PowerWordContent.powerBound D cutoff L) _ _
    (induced_killsWeightedCoefficients D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν))
      (weightedRestriction_kills D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)))
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i]))
    (oldComparison D Sc cutoff L ν i) w
    (BalancedInduction.tensor (append D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)).toFunctor (OldCategory.mk ν) g
      (PowerWordYoneda.unitVector D Sc cutoff L ν))
  have hi := inverse_tensor_steps
    (appendWeightedModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν)) (descendedComparison D Sc cutoff L ν i)
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj w)
    _ _ _ he (hf.trans (oldComparison_tensor_unit D Sc cutoff L ν i w g))
  rw [weightedAppendIso_eq]
  dsimp only [PowerWordContent.weightedWord, BalancedInduction.induction] at hi ⊢
  convert hi using 1

private theorem forward_steps {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M P N : Superfunctor k C (SVec k)} (e : M ≅ P) (f : P ≅ N)
    (w : C) (b : M.obj w) (c : P.obj w) (z : N.obj w)
    (he : e.hom.total w b = c) (hf : f.hom.total w c = z) :
    ((e ≪≫ f).hom.total w) b = z := by
  rw [Iso.trans_hom, Superfunctor.comp_total, SVec.comp_apply, he, hf]

private def extendedComparison (ν : List I) (i : I) :
    BalancedInduction.induced (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
      (BalancedInduction.induced
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν)) ≅
    PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]) :=
  (BalancedInduction.induction (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])).mapIso
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν) ≪≫ PowerWordContent.weightedAppendIso D Sc cutoff L ν i

private theorem contentExtension_unit (ν : List I)
    (s : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
    (b : (PowerWordContent.contentWord D Sc cutoff L ν).obj s) :
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν).hom.total s.obj
      (BalancedInduction.unit
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor s b) = b := by
  change BalancedInduction.counit
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
    (PowerWordContent.weightedWord D Sc cutoff L ν).toFunctor s.obj
      (BalancedInduction.unit
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor s b) + 0 = b
  rw [add_zero]
  exact LinearMap.congr_fun (BalancedInduction.counit_unit
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
    (PowerWordContent.weightedWord D Sc cutoff L ν).toFunctor s) b

set_option backward.dsimp.instances true in
private theorem extendedComparison_tensor_unit (ν : List I) (i : I)
    (w : OldCategory D Sc cutoff) (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ w) :
    (extendedComparison D Sc cutoff L ν i).hom.total
      ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj w)
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
        (BalancedInduction.induced
          (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
          (PowerWordContent.contentWord D Sc cutoff L ν)).toFunctor
        ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj (OldCategory.mk ν))
        ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map
          (X := (append D Sc cutoff i).obj (OldCategory.mk ν)) (Y := w) g)
        (BalancedInduction.unit
          (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
          (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor
          (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl)
          (PowerWordYoneda.unitVector D Sc cutoff L ν))) =
    powerWordGenerator D Sc cutoff L (ν ++ [i]) w g := by
  have hh := mapped_tensor_steps
    (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
    (M := BalancedInduction.induced
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
      (PowerWordContent.contentWord D Sc cutoff L ν))
    (P := PowerWordContent.weightedWord D Sc cutoff L ν)
    (N := PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]))
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν)
    (PowerWordContent.weightedAppendIso D Sc cutoff L ν i)
    (PowerWordContentDot.contentExtension_even D Sc cutoff L ν)
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj (OldCategory.mk ν))
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).obj w)
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map
      (X := (append D Sc cutoff i).obj (OldCategory.mk ν)) (Y := w) g)
    (BalancedInduction.unit
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
      (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl)
      (PowerWordYoneda.unitVector D Sc cutoff L ν))
    (PowerWordYoneda.unitVector D Sc cutoff L ν)
    (powerWordGenerator D Sc cutoff L (ν ++ [i]) w g)
    (contentExtension_unit D Sc cutoff L ν
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl) _)
    (weighted_append_tensor_unit D Sc cutoff L ν i w g)
  dsimp only [extendedComparison, BalancedInduction.induction] at hh ⊢
  convert hh using 1

private theorem restriction_total {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M P : Superfunctor k B (SVec k)} (f : M ⟶ P) (w : C) :
    ((BalancedInduction.restriction Q).map f).total w = f.total (Q.obj w) := rfl

private theorem contentAppendIso_eq (ν : List I) (i : I) :
    PowerWordContent.contentAppendIso D Sc cutoff L ν i =
      contentAppendToRestrictionIso D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (ν : Multiset I) [i] ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i])
        (PowerWordContent.contentWord D Sc cutoff L ν) ≪≫
      (BalancedInduction.restriction
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
          ((ν ++ [i] : List I) : Multiset I))).mapIso (extendedComparison D Sc cutoff L ν i) := rfl

/-- The literal selected content append comparison retains the entire
old-arrow tail on the coefficient unit. -/
theorem content_append_tensor_unit (ν : List I) (i : I)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      ((ν ++ [i] : List I) : Multiset I))
    (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ OldCategory.mk w.obj.word) :
    (PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom.total w
      (BalancedInduction.tensor
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) [i]
          ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]))
        (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl)
        (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν ++ [i]) w.obj.word g)
        (PowerWordYoneda.unitVector D Sc cutoff L ν)) =
    powerWordGenerator D Sc cutoff L (ν ++ [i]) (OldCategory.mk w.obj.word) g := by
  have hf := extendedComparison_tensor_unit D Sc cutoff L ν i (OldCategory.mk w.obj.word) g
  rw [contentAppendIso_eq, Iso.trans_hom, Functor.mapIso_hom,
    Superfunctor.comp_total, SVec.comp_apply]
  rw [restriction_total, ← contentAppendToRestrictionLinear_eq_selected]
  rw [contentAppendToRestrictionLinear_tensor]
  convert hf using 1

end OddMath.QuiverHecke.ELVOld.PowerWordAppendUnits

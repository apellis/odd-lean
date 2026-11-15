import OddMath.QuiverHecke.CyclotomicAction.PowerWordContent
import OddMath.QuiverHecke.CyclotomicAction.DistinctCrossing
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.WeightPair
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.ContentModule

/-!
# Power word whiskering

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Selected word append comparison on cyclic unit tensors

SwappedVacuumCoordinates §4: compute the independently chosen comparison
on a regular coefficient unit and an arbitrary full old-arrow tail. Together
with proved cyclicity this supports comparison of whole chosen crossing maps.
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

omit [Fintype I] in
private theorem weighted_carrier_eq (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (w : OldCategory D Sc cutoff) :
    ((weightedModule D Sc cutoff N M hM).obj ((oldTruncateFunctor D Sc cutoff N).obj w)).carrier =
      (M.obj w).carrier := rfl

private def extendedLinear (ν : List I) (i : I)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      ((ν ++ [i] : List I) : Multiset I)) :
    BalancedInduction.Obj (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
      (BalancedInduction.induced
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν)).toFunctor w.obj →ₗ[k]
      BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor (OldCategory.mk w.obj.word) :=
  (extendedComparison D Sc cutoff L ν i).hom.total w.obj

private def contentLinear (ν : List I) (i : I)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      ((ν ++ [i] : List I) : Multiset I)) :
    BalancedInduction.Obj
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) [i]
        ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]))
      (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor w →ₗ[k]
      BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor (OldCategory.mk w.obj.word) :=
  (PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom.total w

private theorem contentLinear_factor (ν : List I) (i : I)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      ((ν ++ [i] : List I) : Multiset I)) :
    contentLinear D Sc cutoff L ν i w = (extendedLinear D Sc cutoff L ν i w).comp
      (contentAppendToRestrictionLinear D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (ν : Multiset I) [i] ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i])
        (PowerWordContent.contentWord D Sc cutoff L ν) w) := by
  unfold contentLinear extendedLinear
  rw [contentAppendIso_eq, Iso.trans_hom, Functor.mapIso_hom,
    Superfunctor.comp_total, restriction_total]
  rfl

set_option backward.dsimp.instances true in
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
  change contentLinear D Sc cutoff L ν i w _ = _
  rw [contentLinear_factor, LinearMap.comp_apply, contentAppendToRestrictionLinear_tensor]
  have hh := extendedComparison_tensor_unit D Sc cutoff L ν i (OldCategory.mk w.obj.word) g
  convert hh using 1
  · exact ((weighted_carrier_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (powerWordModule D Sc cutoff L (ν ++ [i]))
      (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i])) (OldCategory.mk w.obj.word)).trans
      (induced_carrier_eq (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L) (OldCategory.mk w.obj.word))).symm
  · unfold extendedLinear
    apply congrArg ((extendedComparison D Sc cutoff L ν i).hom.total w.obj)
    rfl

end OddMath.QuiverHecke.ELVOld.PowerWordAppendUnits
end

end

section

/-! # Selected word comparison and induction of signed old-Hom maps

SwappedVacuumCoordinates §§4–5 require compatibility with arbitrary right
contexts, beyond the last dot and crossing. The selected append comparison
is used to identify the independently induced old-Hom module map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWhiskering
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t : List I) (i : I)

private def comparisonIso {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction K).obj (BalancedInduction.induced J R) ≅
      (BalancedInduction.induction P).obj R := (inductionCompOfEq J K P e).app R

private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
section Inner
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J₀ J₁ : C ⥤ B) (K : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J₀.Additive] [J₀.Linear k] [IsSuperfunctor k J₀]
  [J₁.Additive] [J₁.Linear k] [IsSuperfunctor k J₁]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J₀ ⋙ K = P₀) (e₁ : J₁ ⋙ K = P₁)
  {p : ZMod 2} {α : ∀ v, J₀.obj v ⟶ J₁.obj v} (hα : IsSupernatural k p α)
  {β : ∀ v, P₀.obj v ⟶ P₁.obj v} (hβ : IsSupernatural k p β)
  (R : Superfunctor k C (SVec k))
end Inner

section Chosen
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J₀ J₁ : C ⥤ B) (K : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J₀.Additive] [J₀.Linear k] [IsSuperfunctor k J₀]
  [J₁.Additive] [J₁.Linear k] [IsSuperfunctor k J₁]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J₀ ⋙ K = P₀) (e₁ : J₁ ⋙ K = P₁)
  {p : ZMod 2} {α : ∀ v, J₀.obj v ⟶ J₁.obj v} (hα : IsSupernatural k p α)
  {β : ∀ v, P₀.obj v ⟶ P₁.obj v} (hβ : IsSupernatural k p β)
  (R : Superfunctor k C (SVec k))
end Chosen

end OddMath.QuiverHecke.ELVOld.PowerWordWhiskering
end

end

section

/-! # Right contexts for the chosen regular-power word action

SwappedVacuumCoordinates §§4–5: iterate the independently chosen append
functors and their selected comparisons, retaining both parity components
of every old arrow and the full coefficient-power quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContexts
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Successive literal right appends, with endpoints fixed recursively. -/
def extendedWord (s : List I) : List I → List I
  | [] => s
  | i :: η => extendedWord (s ++ [i]) η

theorem extendedWord_eq (s η : List I) : extendedWord s η = s ++ η := by
  induction η generalizing s with
  | nil => simp [extendedWord]
  | cons i η ih => simpa only [extendedWord, List.append_assoc, List.singleton_append] using ih (s ++ [i])

/-- The literal composite of the existing append induction functors. -/
def contextInduction : List I →
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k)
  | [] => 𝟭 _
  | i :: η => BalancedInduction.induction (append D Sc cutoff i) ⋙ contextInduction η

/-- The old arrow is extended by those same append functors. -/
def extendedArrow (s t : List I) : (η : List I) →
    ((OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) →
    ((OldCategory.mk (extendedWord t η) : OldCategory D Sc cutoff) ⟶ OldCategory.mk (extendedWord s η))
  | [], g => g
  | i :: η, g => extendedArrow (s ++ [i]) (t ++ [i]) η ((append D Sc cutoff i).map g)

/-- Only the existing selected single append isomorphisms are composed. -/
def contextIso (s : List I) : (η : List I) →
    (contextInduction D Sc cutoff η).obj (powerWordModule D Sc cutoff L s) ≅
      powerWordModule D Sc cutoff L (extendedWord s η)
  | [] => Iso.refl _
  | i :: η => (contextInduction D Sc cutoff η).mapIso (powerWordAppendIso D Sc cutoff L s i) ≪≫
      contextIso (s ++ [i]) η

private def contextEquation (s t η : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) : Prop :=
  (contextInduction D Sc cutoff η).map (PowerWordMorphisms.fromArrow D Sc cutoff L s t g) ≫
      (contextIso D Sc cutoff L t η).hom =
    (contextIso D Sc cutoff L s η).hom ≫
      PowerWordMorphisms.fromArrow D Sc cutoff L (extendedWord s η) (extendedWord t η)
        (extendedArrow D Sc cutoff s t η g)

private theorem comparison_step {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (K : C ⥤ B) (H : B ⥤ E) {P Q : C} {V W : B} {S T : E}
    (e : K.obj P ≅ V) (f : K.obj Q ≅ W) (c : H.obj V ≅ S) (d : H.obj W ≅ T)
    (x : P ⟶ Q) (y : V ⟶ W) (z : S ⟶ T)
    (h₀ : K.map x ≫ f.hom = e.hom ≫ y) (h₁ : H.map y ≫ d.hom = c.hom ≫ z) :
    (K ⋙ H).map x ≫ (H.mapIso f ≪≫ d).hom = (H.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← H.map_comp, h₀, H.map_comp, Category.assoc, h₁]

end OddMath.QuiverHecke.ELVOld.PowerWordContexts
end

end

section

/-! # Signed composition in the full regular-power word chart

SwappedVacuumCoordinates §§4–5: the super-opposite composition sign in the
old-Hom word chart is retained before combining it with the signed half-turn.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordComposition
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t u : List I)

/-- Signed old-Hom maps retain scalar multiplication. -/
theorem fromArrow_smul (a : k)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordMorphisms.fromArrow D Sc cutoff L s t (a • g) =
      a • PowerWordMorphisms.fromArrow D Sc cutoff L s t g := by
  unfold PowerWordMorphisms.fromArrow
  rw [map_smul]
  exact (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).symm.map_smul a _

private theorem evaluate_fromArrow
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t g) =
    powerWordGenerator D Sc cutoff L t (OldCategory.mk s) g :=
  PowerWordYoneda.evaluate_fromElement D Sc cutoff L s (powerWordObject D Sc cutoff L t) _

/-- Whole-map super-opposite composition, on every full coefficient vector. -/
theorem fromArrow_comp {p q : ZMod 2}
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (f : (OldCategory.mk u : OldCategory D Sc cutoff) ⟶ OldCategory.mk t)
    (hg : g ∈ parity (R := k) _ _ p) (hf : f ∈ parity (R := k) _ _ q) :
    PowerWordMorphisms.fromArrow D Sc cutoff L s t g ≫
        PowerWordMorphisms.fromArrow D Sc cutoff L t u f =
      sign k (p * q) • PowerWordMorphisms.fromArrow D Sc cutoff L s u (f ≫ g) := by
  apply (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L u)).injective
  rw [map_smul]
  change PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L u) _ =
    sign k (p * q) • PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L u) _
  rw [evaluate_fromArrow]
  change _ + _ = _
  dsimp only [PowerWordYoneda.unitVector, powerWordObject] at ⊢
  erw [PowerWordMorphisms.composition_generator, PowerWordMorphisms.composition_generator]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 1) hg (by decide), proj_of_mem_ne (p := 1) hf (by decide),
      Supercategory.sign]
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 1) hg (by decide), proj_of_mem_ne (p := 0) hf (by decide),
      Supercategory.sign]
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 0) hg (by decide), proj_of_mem_ne (p := 1) hf (by decide),
      Supercategory.sign]
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 0) hg (by decide), proj_of_mem_ne (p := 0) hf (by decide),
      Supercategory.sign]

/-- The half-turn followed by the literal old quotient retains total
coefficient-plus-affine parity. -/
theorem halfTurnOldHom_mem {s t : List I} {p : ZMod 2}
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    (hf : f ∈ parity (R := k) _ _ p) :
    halfTurnOldHom D Sc cutoff s t f ∈ parity (R := k) _ _ p := by
  apply Submodule.mem_map_of_mem
  exact elvQuotientMap_mem D (parameterTwist D Sc) cutoff (htCoef_mem_parity D Sc hf)

/-- Full source arrows act in the actual word-module chart at twisted
parameters. This map is not yet identified with the chosen weight action. -/
def sourceMap (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) →ₗ[k]
      (powerWordModule D (parameterTwist D Sc) cutoff L s.reverse ⟶
        powerWordModule D (parameterTwist D Sc) cutoff L t.reverse) :=
  (PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
    (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse)).symm.toLinearMap.comp
    ((powerWordGenerator D (parameterTwist D Sc) cutoff L t.reverse (OldCategory.mk s.reverse)).comp
      (halfTurnOldHom D Sc cutoff s t))

theorem sourceMap_apply (s t : List I) (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    sourceMap D Sc cutoff L s t f =
      PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L s.reverse t.reverse
        (halfTurnOldHom D Sc cutoff s t f) := rfl

/-- The two super-opposite signs match, so source chronological composition
is ordinary composition of the actual word module maps. -/
theorem sourceMap_comp_homogeneous {s t u : List I} {p q : ZMod 2}
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    {g : coefficientObj D Sc t ⟶ coefficientObj D Sc u}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ q) :
    sourceMap D Sc cutoff L s u (f ≫ g) =
      sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g := by
  rw [sourceMap_apply, sourceMap_apply, sourceMap_apply, halfTurnOldHom_comp D Sc cutoff hf hg,
    fromArrow_smul, ← SKM.sign_eq_zsign]
  exact (fromArrow_comp D (parameterTwist D Sc) cutoff L s.reverse t.reverse u.reverse _ _
    (halfTurnOldHom_mem D Sc cutoff hf) (halfTurnOldHom_mem D Sc cutoff hg)).symm

/-- Ordinary source composition for arbitrary full coefficient arrows,
including both parity components of each input. -/
theorem sourceMap_comp {s t u : List I}
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t)
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc u) :
    sourceMap D Sc cutoff L s u (f ≫ g) =
      sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g := by
  revert g
  refine Supercategory.induction_on (R := k)
    (P := fun f => ∀ g : coefficientObj D Sc t ⟶ coefficientObj D Sc u,
      sourceMap D Sc cutoff L s u (f ≫ g) =
        sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g) f ?_ ?_ ?_
  · intro g
    simp only [Limits.zero_comp, map_zero]
  · intro p f hf g
    refine Supercategory.induction_on (R := k)
      (P := fun g => sourceMap D Sc cutoff L s u (f ≫ g) =
        sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g) g ?_ ?_ ?_
    · simp only [Limits.comp_zero, map_zero]
    · intro q g hg
      exact sourceMap_comp_homogeneous D Sc cutoff L hf hg
    · intro g h ihg ihh
      simp only [Preadditive.comp_add, map_add, ihg, ihh]
  · intro f h ihf ihh g
    simp only [Preadditive.add_comp, map_add, ihf g, ihh g]

/-- Evaluating this module map at the word unit recovers the previously
computed coordinate in the actual module. It is not a chosen weight-action
identification. -/
theorem sourceMap_evaluate (s t : List I)
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
      (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse)
      (sourceMap D Sc cutoff L s t f) = powerWordHalfTurnCoordinate D Sc cutoff L s t f := by
  change (PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
    (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse))
      ((PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
        (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse)).symm
        (powerWordGenerator D (parameterTwist D Sc) cutoff L t.reverse (OldCategory.mk s.reverse)
          (halfTurnOldHom D Sc cutoff s t f))) = _
  rw [LinearEquiv.apply_symm_apply, powerWordHalfTurnCoordinate_eq]
  rfl

end OddMath.QuiverHecke.ELVOld.PowerWordComposition
end

end

section

/-! # Chosen content crossings in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: identify the chosen content-induction
crossing with the signed old-Hom operator through the prescribed append
comparisons, retaining all exterior coefficients and intermediate labels. -/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentCross
universe u
section Generic
variable {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
open BalancedInduction
private def mapLinear {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (w : B) :
    Obj J M.toFunctor w →ₗ[k] Obj J N.toFunctor w := (moduleMap J f).total w

 theorem even_unit_components {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (s : C) (b : M.obj s) (c : N.obj s)
    (hb : b ∈ (M.obj s).part 0) (hc : c ∈ (N.obj s).part 0)
    (h : f.total s b = c) : f.app 0 s b = c ∧ f.app 1 s b = 0 := by
  have h0 := SVec.apply_mem_part (f.app_mem 0 s) hb
  have h1 := SVec.apply_mem_part (f.app_mem 1 s) hb
  rw [zero_add] at h0 h1
  have hp0 := congrArg ((N.obj s).proj 0) h
  have hp1 := congrArg ((N.obj s).proj 1) h
  change (N.obj s).proj 0 (f.app 0 s b + f.app 1 s b) = _ at hp0
  change (N.obj s).proj 1 (f.app 0 s b + f.app 1 s b) = _ at hp1
  rw [map_add, SVec.proj_apply_of_mem_part _ h0, SVec.proj_apply_of_mem_part _ h1,
    SVec.proj_apply_of_mem_part _ hc] at hp0 hp1
  have hz : (0 : ZMod 2) ≠ 1 := by decide
  have ho : (1 : ZMod 2) ≠ 0 := by decide
  constructor
  · simpa only [ite_true, hz, ho, ite_false, add_zero] using hp0
  · simpa only [hz, ho, ite_false, ite_true, zero_add] using hp1

private theorem moduleMap_tensor_even_unit {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (s : C) (w : B) (g : J.obj s ⟶ w) (b : M.obj s) (c : N.obj s)
    (hb : b ∈ (M.obj s).part 0) (hc : c ∈ (N.obj s).part 0)
    (h : f.total s b = c) :
    mapLinear J f w (tensor J M.toFunctor s g b) = tensor J N.toFunctor s g c := by
  change (moduleMap J f).total w _ = _
  obtain ⟨h0,h1⟩ := even_unit_components f s b c hb hc h
  rw [moduleMap_total_tensor, h0, h1, tensor_zero_right, add_zero]
section Rectangular
variable {A E : Type u} [Category.{u} A] [Category.{u} E]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive E] [Linear k E] [Supercategory k E]

private def doubleUnit (K : B ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) :
    (induced K (induced J M)).obj (K.obj (J.obj s)) :=
  unit K (induced J M).toFunctor (J.obj s) (unit J M.toFunctor s b)

private theorem rectangle_unit
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (T ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) :
    (rectangularCrossComponent T K L U hα M).total (U.obj (K.obj s)) (doubleUnit K U M s b) =
      tensor L (induced T M).toFunctor (T.obj s) (α s) (unit T M.toFunctor s b) := by
  simp only [doubleUnit, unit_apply]
  erw [rectangularCrossComponent_total_tensor, CategoryTheory.Functor.map_id,
    Category.id_comp, twist_id, Category.comp_id]
private theorem rectangle_unit_image
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (T ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))
    {P : Superfunctor k E (SVec k)} (eT : induced L (induced T M) ≅ P)
    (s : C) (b : M.obj s) (a : L.obj (T.obj s) ⟶ U.obj (K.obj s))
    (z : P.obj (U.obj (K.obj s))) (hc : α s = a)
    (hr : eT.hom.total (U.obj (K.obj s))
      (tensor L (induced T M).toFunctor (T.obj s) a (unit T M.toFunctor s b)) = z) :
    eT.hom.total (U.obj (K.obj s))
      ((rectangularCrossComponent T K L U hα M).total (U.obj (K.obj s))
        (doubleUnit K U M s b)) = z := by
  have h₁ := congrArg (eT.hom.total (U.obj (K.obj s))) (rectangle_unit T K L U hα M s b)
  have h₂ := congrArg (fun g : L.obj (T.obj s) ⟶ U.obj (K.obj s) =>
    eT.hom.total (U.obj (K.obj s))
      (tensor L (induced T M).toFunctor (T.obj s) g (unit T M.toFunctor s b))) hc
  exact h₁.trans (h₂.trans hr)

end Rectangular

private theorem comp_total_eval {M N P : Superfunctor k C (SVec k)}
    (f : M ⟶ N) (g : N ⟶ P) (w : C) (x : M.obj w) :
    (f ≫ g).total w x = g.total w (f.total w x) := by
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem inverse_at_image {M N : Superfunctor k C (SVec k)} (e : M ≅ N)
    (w : C) (b : M.obj w) (c : N.obj w) (h : e.hom.total w b = c) :
    e.inv.total w c = b := by
  have hi := (moduleIsoLinearEquiv e w).symm_apply_apply b
  change e.inv.total w (e.hom.total w b) = b at hi
  rw [h] at hi
  exact hi

private theorem family_apply_heq {ι : Type u} {A B : ι → Type u}
    (F : ∀ x, A x → B x) {x y : ι} (h : x = y) {a : A x} {b : A y} (hab : HEq a b) :
    HEq (F x a) (F y b) := by
  cases h
  cases hab
  rfl

private theorem eq_of_heq_square {A B : Type u} {a b : A} {c d : B}
    (hac : HEq a c) (hab : a = b) (hbd : HEq b d) : c = d :=
  eq_of_heq (hac.symm.trans ((heq_of_eq hab).trans hbd))

private theorem hom_ext_transfer {M N : Superfunctor k C (SVec k)}
    {x y : C} (hxy : x = y) (b : M.obj x) (c : M.obj y) (hbc : HEq b c)
    (H : Function.Injective (fun f : M ⟶ N => f.total x b)) :
    Function.Injective (fun f : M ⟶ N => f.total y c) := by
  cases hxy
  cases hbc
  exact H

end Generic
open CyclotomicCrossingTensor
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem contentAppendIsoTo_canonical (ν : List I) (i : I) :
    PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i (ν : Multiset I)
      ((ν ++ [i] : List I) : Multiset I) rfl (Multiset.coe_add ν [i]) =
      PowerWordContent.contentAppendIso D Sc cutoff L ν i := rfl

/-- The same frozen selected append comparison at arbitrary equal content labels. -/
theorem content_append_tensor_unit_to (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hγ : β + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ)
    (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ OldCategory.mk w.obj.word) :
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hγ).hom.total w
      (BalancedInduction.tensor
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hγ)
        (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
        (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν ++ [i]) w.obj.word g)
        (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν)) =
    powerWordGenerator D Sc cutoff L (ν ++ [i]) (OldCategory.mk w.obj.word) g := by
  subst β
  have h : γ = ((ν ++ [i] : List I) : Multiset I) := hγ.symm.trans (Multiset.coe_add ν [i])
  cases h
  rw [contentAppendIsoTo_canonical]
  have hh := PowerWordAppendUnits.content_append_tensor_unit D Sc cutoff L ν i w g
  convert hh using 1
  · rfl
  · apply congrArg ((PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom.total w)
    rfl

omit [Fintype I] in
/-- The source word's content equality after the given append step. -/
theorem appendContentEq (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ) :
    ((ν ++ [i] : List I) : Multiset I) = γ :=
  (Multiset.coe_add ν [i]).symm.trans ((congrArg (fun δ => δ + ([i] : Multiset I)) hν).trans hi)

/-- The chosen append comparison sends its actual coend unit to the next word unit. -/
theorem append_unit_to (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ) :
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi).hom.total
      ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi).obj
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν))
      (BalancedInduction.unit
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi)
        (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
        (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν)) =
      PowerWordContentCyclicity.wordUnit D Sc cutoff L (ν ++ [i]) γ
        (appendContentEq ν i β γ hν hi) := by
  have hh := content_append_tensor_unit_to D Sc cutoff L ν i β γ hν hi
    ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi).obj
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)) (𝟙 _)
  convert hh using 1
  · apply congrArg ((PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi).hom.total _)
    rw [BalancedInduction.unit_apply]
    rfl
  · rfl

/-- Recursively chosen single-append comparisons, retaining both actual intermediate labels. -/
def pairIsoTo (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ) :
    BalancedInduction.induced
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
      (BalancedInduction.induced
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
        (PowerWordWeight.wordAt D Sc cutoff L ν β)) ≅
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ :=
  (BalancedInduction.induction
    (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)).mapIso
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j β δ hν hj) ≪≫
    PowerWordWeight.contentAppendIsoTo D Sc cutoff L (ν ++ [j]) i δ γ
      (appendContentEq ν j β δ hν hj) hi

private def appendLinearTo (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ) :
    BalancedInduction.Obj
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi)
      (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor w →ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L (ν ++ [i]) γ).obj w :=
  (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi).hom.total w

private def pairLinear (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ) :
    BalancedInduction.Obj
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
      (BalancedInduction.induced
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
        (PowerWordWeight.wordAt D Sc cutoff L ν β)).toFunctor w →ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ).obj w :=
  (pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total w

private theorem pairLinear_factor (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ) :
    pairLinear D Sc cutoff L ν i j β δ γ hν hj hi w =
      (appendLinearTo D Sc cutoff L (ν ++ [j]) i δ γ
        (appendContentEq ν j β δ hν hj) hi w).comp
      (mapLinear
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
        (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j β δ hν hj).hom w) := by
  unfold pairLinear pairIsoTo mapLinear appendLinearTo
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total]
  rfl

/-- The recursively selected pair comparison on an arbitrary entire old-arrow
tail and the nested actual coefficient unit. -/
theorem pair_tensor_unit (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ)
    (g : (OldCategory.mk ((ν ++ [j]) ++ [i]) : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    (pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total w
      (BalancedInduction.tensor
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
        (BalancedInduction.induced
          (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
          (PowerWordWeight.wordAt D Sc cutoff L ν β)).toFunctor
        ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj).obj
          (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν))
        (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) ((ν ++ [j]) ++ [i]) w.obj.word g)
        (BalancedInduction.unit
          (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
          (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor
          (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
          (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν))) =
      powerWordGenerator D Sc cutoff L ((ν ++ [j]) ++ [i]) (OldCategory.mk w.obj.word) g := by
  let J := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj
  let U := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi
  let M := PowerWordWeight.wordAt D Sc cutoff L ν β
  let s := PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν
  let b := PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν
  let c := PowerWordContentCyclicity.wordUnit D Sc cutoff L (ν ++ [j]) δ (appendContentEq ν j β δ hν hj)
  have hb := SVec.apply_mem_part (BalancedInduction.unit_mem J M s)
    (PowerWordContentCyclicity.wordUnit_even D Sc cutoff L ν β hν)
  rw [zero_add] at hb
  have hm := moduleMap_tensor_even_unit U
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j β δ hν hj).hom
    (J.obj s) w
    (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) ((ν ++ [j]) ++ [i]) w.obj.word g)
    (BalancedInduction.unit J M.toFunctor s b) c hb
    (PowerWordContentCyclicity.wordUnit_even D Sc cutoff L (ν ++ [j]) δ
      (appendContentEq ν j β δ hν hj))
    (append_unit_to D Sc cutoff L ν j β δ hν hj)
  change pairLinear D Sc cutoff L ν i j β δ γ hν hj hi w _ = _
  rw [pairLinear_factor, LinearMap.comp_apply]
  rw [hm]
  have hh := content_append_tensor_unit_to D Sc cutoff L (ν ++ [j]) i δ γ
    (appendContentEq ν j β δ hν hj) hi w g
  change appendLinearTo D Sc cutoff L (ν ++ [j]) i δ γ
    (appendContentEq ν j β δ hν hj) hi w _ = _ at hh
  convert hh using 1
  apply congrArg (appendLinearTo D Sc cutoff L (ν ++ [j]) i δ γ
    (appendContentEq ν j β δ hν hj) hi w)
  rfl

/-- The recursively chosen pair comparison sends the literal nested coend
unit to the actual next-word unit at the same prescribed content. -/
private theorem pair_unit_to (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ) :
    let K := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj
    let U := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi
    (pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total
      (U.obj (K.obj (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)))
      (doubleUnit K U (PowerWordWeight.wordAt D Sc cutoff L ν β)
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
        (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν)) =
      PowerWordContentCyclicity.wordUnit D Sc cutoff L ((ν ++ [j]) ++ [i]) γ
        (appendContentEq (ν ++ [j]) i δ γ (appendContentEq ν j β δ hν hj) hi) := by
  dsimp only
  have hh := pair_tensor_unit D Sc cutoff L ν i j β δ γ hν hj hi
    ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi).obj
      ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj).obj
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν))) (𝟙 _)
  convert hh using 1
  · apply congrArg ((pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total _)
    simp only [doubleUnit, BalancedInduction.unit_apply]
    rfl
  · rfl

/-- The already chosen full old-Hom map, descended on the unchanged word carriers. -/
def weightedWordArrow (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordContent.weightedWord D Sc cutoff L s ⟶ PowerWordContent.weightedWord D Sc cutoff L t :=
  weightedModuleHom D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L s) (powerWordModule D Sc cutoff L t)
    (PowerWordContent.word_killsWeighted D Sc cutoff L s)
    (PowerWordContent.word_killsWeighted D Sc cutoff L t)
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g)

/-- Exact-content restriction of the actual full-coefficient word operator. -/
def contentWordArrow (β : Multiset I) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordWeight.wordAt D Sc cutoff L s β ⟶ PowerWordWeight.wordAt D Sc cutoff L t β :=
  (BalancedInduction.restriction
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)).map
    (weightedWordArrow D Sc cutoff L s t g)

/-- Both homogeneous components are literally retained through descent and restriction. -/
theorem contentWordArrow_total (β : Multiset I) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β) :
    (contentWordArrow D Sc cutoff L β s t g).total w =
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t g).total (OldCategory.mk w.obj.word) := rfl

/-- Evaluation on the actual even word unit is the full old-arrow generator. -/
theorem contentWordArrow_unit (β : Multiset I) (s t : List I) (hs : (s : Multiset I) = β)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    (contentWordArrow D Sc cutoff L β s t g).total
      (PowerWordContentCyclicity.wordObject D Sc cutoff L s β hs)
      (PowerWordContentCyclicity.wordUnit D Sc cutoff L s β hs) =
      powerWordGenerator D Sc cutoff L t (OldCategory.mk s) g := by
  rw [contentWordArrow_total]
  change PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g) = _
  exact (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).apply_symm_apply _

/-- The original normalized physical crossing, with the required extra minus
in equal colour and positive representative in distinct colours. -/
def normalizedOldCross (ν : List I) (i j : I) :
    (OldCategory.mk ((ν ++ [i]) ++ [j]) : OldCategory D Sc cutoff) ⟶
      OldCategory.mk ((ν ++ [j]) ++ [i]) :=
  if i = j then -Distinct.crossComponent D Sc cutoff j i (OldCategory.mk ν)
  else Distinct.crossComponent D Sc cutoff j i (OldCategory.mk ν)

/-- The full signed old-Hom crossing in the actual scheduled content word carriers. -/
def wordCross (β : Multiset I) (ν : List I) (i j : I) :
    PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) β ⟶
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) β :=
  contentWordArrow D Sc cutoff L β ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j])
    (normalizedOldCross D Sc cutoff ν i j)

/-- The normalized physical crossing descends literally through the actual
old-to-weighted quotient at every prescribed content successor. -/
theorem normalizedOldCross_quotient (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β)
    (i j : I) (δj δi γ : Multiset I)
    (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
    (hSource : δj + ([i] : Multiset I) = γ) (hTarget : δi + ([j] : Multiset I) = γ) :
    (oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map
      (normalizedOldCross D Sc cutoff ν i j) =
      normalizedContentTargetsCross D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        β j i δi δj γ hi hj hTarget hSource
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν) := by
  by_cases h : i = j
  · subst j
    simp only [normalizedOldCross, normalizedContentTargetsCross, contentDistinctTargetsCross, ite_true,
      Functor.map_neg, oldTruncateFunctor_map_distinctCross]
    rfl
  · simp only [normalizedOldCross, normalizedContentTargetsCross, ite_eq_right h,
      ite_eq_right (Ne.symm h)]
    exact oldTruncateFunctor_map_distinctCross D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      j i (OldCategory.mk ν)

omit [Fintype I] in
private theorem append_obj_word (N : ℕ) (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (s : ContentCategory D Sc cutoff N β) :
    ((contentAppendTo D Sc cutoff N β σ γ h).obj s).obj.word = s.obj.word ++ σ := rfl

private theorem wordObject_word (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β) :
    (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν).obj.word = ν := rfl

omit [Fintype I] in
private theorem pairContentEq (β δ γ : Multiset I) (i j : I)
    (hj : β + ([j] : Multiset I) = δ) (hi : δ + ([i] : Multiset I) = γ) :
    β + ([j,i] : Multiset I) = γ := by
  change β + (([j] ++ [i] : List I) : Multiset I) = γ
  rw [← Multiset.coe_add, ← add_assoc, hj, hi]

section UnitWord
variable (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β)
  (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hSource : δj + ([i] : Multiset I) = γ) (hTarget : δi + ([j] : Multiset I) = γ)
local notation "CT" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] δi hi
local notation "CK" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δj hj
local notation "CL" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δi [j] γ hTarget
local notation "CU" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δj [i] γ hSource
local notation "CM" => PowerWordWeight.wordAt D Sc cutoff L ν β
local notation "CS" => PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν
local notation "CB" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν
local notation "CW" => CategoryTheory.Functor.obj CU (CategoryTheory.Functor.obj CK CS)
local notation "CH" => normalizedContentTargetsCross_supernatural D Sc cutoff (PowerWordContent.powerBound D cutoff L)
  β j i δi δj γ hi hj hTarget hSource
local notation "ET" => pairIsoTo D Sc cutoff L ν j i β δi γ hν hi hTarget
local notation "CG" => normalizedOldCross D Sc cutoff ν i j
local notation "CA" => truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L)
  ((ν ++ [i]) ++ [j]) (TruncatedCategory.word (ContentCategory.obj CW)) CG
local notation "CZ" => powerWordGenerator D Sc cutoff L ((ν ++ [i]) ++ [j]) (OldCategory.mk (TruncatedCategory.word (ContentCategory.obj CW))) CG

private theorem rectangular_unit_word :
    (ET).hom.total CW ((BalancedInduction.rectangularCrossComponent CT CK CL CU CH CM).total CW
      (doubleUnit CK CU CM CS CB)) = CZ := by
  apply rectangle_unit_image CT CK CL CU CH CM ET CS CB CA CZ
  · have hc := normalizedOldCross_quotient D Sc cutoff L ν β hν i j δj δi γ hj hi hSource hTarget
    simpa only [oldTruncateFunctor, append_obj_word, wordObject_word] using hc.symm
  · exact pair_tensor_unit D Sc cutoff L ν j i β δi γ hν hi hTarget CW CG
local notation "ES" => pairIsoTo D Sc cutoff L ν i j β δj γ hν hj hSource
local notation "HS" => appendContentEq (ν ++ [j]) i δj γ (appendContentEq ν j β δj hν hj) hSource
local notation "CSW" => PowerWordContentCyclicity.wordObject D Sc cutoff L ((ν ++ [j]) ++ [i]) γ HS
local notation "CUB" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ((ν ++ [j]) ++ [i]) γ HS
local notation "CX" => BalancedInduction.rectangularCrossComponent CT CK CL CU CH CM
local notation "WW" => wordCross D Sc cutoff L γ ν i j

private theorem inverse_pair_unit :
    (ES).inv.total CW CUB = doubleUnit CK CU CM CS CB := by
  exact inverse_at_image ES CW _ CUB (pair_unit_to D Sc cutoff L ν i j β δj γ hν hj hSource)

/-- The independently chosen normalized rectangular crossing is the full signed
old-Hom word operator through the recursively selected pair comparisons.
All actual intermediate labels and all exterior coefficient vectors are retained. -/
theorem selected_pair_cross :
    CX ≫ (ET).hom = (ES).hom ≫ WW := by
  have hObj : CSW = CW := rfl
  have hExt : Function.Injective (fun f :
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ ⟶
        PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ => f.total CW CUB) := by
    apply hom_ext_transfer hObj CUB CUB (HEq.refl CUB)
    intro f g h
    exact PowerWordContentCyclicity.hom_ext D Sc cutoff L ((ν ++ [j]) ++ [i]) γ HS
      (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ) f g h
  have hconj : (ES).inv ≫ CX ≫ (ET).hom = WW := by
    apply hExt
    change ((ES).inv ≫ CX ≫ (ET).hom).total CW CUB = (WW).total CW CUB
    rw [comp_total_eval, comp_total_eval, inverse_pair_unit]
    have hr := rectangular_unit_word D Sc cutoff L ν β hν i j δj δi γ hj hi hSource hTarget
    have ho := contentWordArrow_unit D Sc cutoff L γ ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) HS CG
    change (WW).total CSW CUB =
      PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j]) γ CSW CG at ho
    have he := family_apply_heq
      (A := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ).obj x)
      (B := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ).obj x)
      (fun x z => (WW).total x z) hObj (HEq.refl CUB)
    have hg := family_apply_heq
      (A := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (OldCategory.mk ((ν ++ [i]) ++ [j]) : OldCategory D Sc cutoff) ⟶ OldCategory.mk x.obj.word)
      (B := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ).obj x)
      (fun x g => PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j]) γ x g)
      hObj (HEq.refl CG)
    have hWord := eq_of_heq_square he ho hg
    change (ET).hom.total CW ((CX).total CW (doubleUnit CK CU CM CS CB)) =
      PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j]) γ CW CG at hr
    exact hr.trans hWord.symm
  have hh := congrArg (fun f => (ES).hom ≫ f) hconj
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh
local notation "HJI" => pairContentEq β δj γ i j hj hSource
local notation "HIJ" => pairContentEq β δi γ j i hi hTarget

end UnitWord

end OddMath.QuiverHecke.ELVOld.PowerWordContentCross
end

end

section

/-! # Arbitrary-arrow append transport in content word coordinates

SwappedVacuumCoordinates §§4–6: the chosen content append comparison must
respect arbitrary full old-Hom maps, including all exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentWhiskering
universe u
section Generic
variable {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
private theorem moduleMap_unit {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (s : C) (b : M.obj s) :
    (BalancedInduction.moduleMap J f).total (J.obj s) (BalancedInduction.unit J M.toFunctor s b) =
      BalancedInduction.unit J N.toFunctor s (f.total s b) := by
  rw [BalancedInduction.unit_apply, BalancedInduction.moduleMap_total_tensor, twist_id]
  change BalancedInduction.tensor J N.toFunctor s (𝟙 _) (f.app 0 s b) +
    BalancedInduction.tensor J N.toFunctor s (𝟙 _) (f.app 1 s b) = _
  rw [← BalancedInduction.tensor_add_right]
  rfl

omit [Supercategory k B] [J.Additive] [J.Linear k] [IsSuperfunctor k J] in
private theorem unit_balance {N : Superfunctor k C (SVec k)} {t s : C}
    (a : t ⟶ s) (b : N.obj t) :
    BalancedInduction.unit J N.toFunctor s (N.map a b) =
      BalancedInduction.tensor J N.toFunctor t (J.map a) b := by
  rw [BalancedInduction.unit_apply]
  exact (BalancedInduction.balance J N.toFunctor a (𝟙 _) b).symm.trans
    (congrArg (fun h => BalancedInduction.tensor J N.toFunctor t h b) (Category.comp_id _))

private theorem moduleMap_unit_image {M N : Superfunctor k C (SVec k)}
    {P : Superfunctor k B (SVec k)} (f : M ⟶ N) (e : BalancedInduction.induced J N ≅ P)
    (s t : C) (a : t ⟶ s) (b : M.obj s) (c : N.obj t) (z : P.obj (J.obj s))
    (hf : f.total s b = N.map a c)
    (he : e.hom.total (J.obj s) (BalancedInduction.tensor J N.toFunctor t (J.map a) c) = z) :
    e.hom.total (J.obj s) ((BalancedInduction.moduleMap J f).total (J.obj s)
      (BalancedInduction.unit J M.toFunctor s b)) = z := by
  rw [moduleMap_unit, hf, unit_balance]
  exact he
private theorem comp_total_eval {M N P : Superfunctor k C (SVec k)}
    (f : M ⟶ N) (g : N ⟶ P) (w : C) (x : M.obj w) :
    (f ≫ g).total w x = g.total w (f.total w x) := by
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem inverse_at_image {M N : Superfunctor k C (SVec k)} (e : M ≅ N)
    (w : C) (b : M.obj w) (c : N.obj w) (h : e.hom.total w b = c) :
    e.inv.total w c = b := by
  have hi := (moduleIsoLinearEquiv e w).symm_apply_apply b
  change e.inv.total w (e.hom.total w b) = b at hi
  rw [h] at hi
  exact hi

private theorem family_apply_heq {ι : Type u} {A B : ι → Type u}
    (F : ∀ x, A x → B x) {x y : ι} (h : x = y) {a : A x} {b : A y} (hab : HEq a b) :
    HEq (F x a) (F y b) := by
  cases h
  cases hab
  rfl

private theorem eq_of_heq_square {A B : Type u} {a b : A} {c d : B}
    (hac : HEq a c) (hab : a = b) (hbd : HEq b d) : c = d :=
  eq_of_heq (hac.symm.trans ((heq_of_eq hab).trans hbd))

private theorem hom_ext_transfer {M N : Superfunctor k C (SVec k)}
    {x y : C} (hxy : x = y) (b : M.obj x) (c : M.obj y) (hbc : HEq b c)
    (H : Function.Injective (fun f : M ⟶ N => f.total x b)) :
    Function.Injective (fun f : M ⟶ N => f.total y c) := by
  cases hxy
  cases hbc
  exact H

end Generic
open CyclotomicCrossingTensor
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t : List I) (i : I) (β γ : Multiset I)
  (hs : (s : Multiset I) = β) (ht : (t : Multiset I) = β)
  (hi : β + ([i] : Multiset I) = γ)
  (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
local notation "J" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi
local notation "M" => PowerWordWeight.wordAt D Sc cutoff L s β
local notation "N" => PowerWordWeight.wordAt D Sc cutoff L t β
local notation "CS" => PowerWordContentCyclicity.wordObject D Sc cutoff L s β hs
local notation "CT" => PowerWordContentCyclicity.wordObject D Sc cutoff L t β ht
local notation "BS" => PowerWordContentCyclicity.wordUnit D Sc cutoff L s β hs
local notation "BT" => PowerWordContentCyclicity.wordUnit D Sc cutoff L t β ht
local notation "W" => CategoryTheory.Functor.obj J CS
local notation "QA" => PowerWordContentCyclicity.arrowFromOld D Sc cutoff L t β ht CS g
local notation "F" => PowerWordContentCross.contentWordArrow D Sc cutoff L β s t g
local notation "ES" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L s i β γ hs hi
local notation "ET" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L t i β γ ht hi
local notation "AG" => CategoryTheory.Functor.map (append D Sc cutoff i) g
local notation "Z" => powerWordGenerator D Sc cutoff L (t ++ [i]) (OldCategory.mk (s ++ [i])) AG

private theorem append_quotient : (J).map QA =
    truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) (t ++ [i]) (s ++ [i]) AG := by
  exact (oldTruncateFunctor_map_append D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
    (OldCategory.mk t) (OldCategory.mk s) g).symm

/-- The chosen append square at its cyclic unit, for a full old arrow. -/
theorem append_unit_arrow :
    (ET).hom.total W ((BalancedInduction.moduleMap J F).total W
      (BalancedInduction.unit J (M).toFunctor CS BS)) = Z := by
  apply moduleMap_unit_image J F ET CS CT QA BS BT Z
  · have hf := PowerWordContentCross.contentWordArrow_unit D Sc cutoff L β s t hs g
    have hg := PowerWordContentCyclicity.generator_as_map_unit D Sc cutoff L t β ht CS g
    exact hf.trans hg.symm
  · rw [append_quotient]
    exact PowerWordContentCross.content_append_tensor_unit_to D Sc cutoff L t i β γ ht hi W AG

local notation "HSI" => PowerWordContentCross.appendContentEq s i β γ hs hi
local notation "CWS" => PowerWordContentCyclicity.wordObject D Sc cutoff L (s ++ [i]) γ HSI
local notation "BSI" => PowerWordContentCyclicity.wordUnit D Sc cutoff L (s ++ [i]) γ HSI
local notation "Y" => PowerWordContentCross.contentWordArrow D Sc cutoff L γ (s ++ [i]) (t ++ [i]) AG

/-- The independently chosen content append comparisons intertwine induction
of every full old-Hom map with its appended arrow, on all coefficient vectors. -/
theorem append_word_arrow :
    (BalancedInduction.induction J).map F ≫ (ET).hom = (ES).hom ≫ Y := by
  have hObj : CWS = W := rfl
  have hExt : Function.Injective (fun f : PowerWordWeight.wordAt D Sc cutoff L (s ++ [i]) γ ⟶
      PowerWordWeight.wordAt D Sc cutoff L (t ++ [i]) γ => f.total W BSI) := by
    apply hom_ext_transfer hObj BSI BSI (HEq.refl BSI)
    intro f g h
    exact PowerWordContentCyclicity.hom_ext D Sc cutoff L (s ++ [i]) γ HSI
      (PowerWordWeight.wordAt D Sc cutoff L (t ++ [i]) γ) f g h
  have hInv := inverse_at_image ES W (BalancedInduction.unit J (M).toFunctor CS BS) BSI
    (PowerWordContentCross.append_unit_to D Sc cutoff L s i β γ hs hi)
  have hconj : (ES).inv ≫ (BalancedInduction.induction J).map F ≫ (ET).hom = Y := by
    apply hExt
    change ((ES).inv ≫ (BalancedInduction.induction J).map F ≫ (ET).hom).total W BSI = (Y).total W BSI
    rw [comp_total_eval, comp_total_eval, hInv]
    have hr := append_unit_arrow D Sc cutoff L s t i β γ hs ht hi g
    have ho := PowerWordContentCross.contentWordArrow_unit D Sc cutoff L γ
      (s ++ [i]) (t ++ [i]) HSI AG
    change (Y).total CWS BSI = PowerWordContentCyclicity.generator D Sc cutoff L (t ++ [i]) γ CWS AG at ho
    have he := family_apply_heq
      (A := fun w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L (s ++ [i]) γ).obj w)
      (B := fun w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L (t ++ [i]) γ).obj w)
      (fun w b => (Y).total w b) hObj (HEq.refl BSI)
    have hg := family_apply_heq
      (A := fun w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (OldCategory.mk (t ++ [i]) : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word)
      (B := fun w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L (t ++ [i]) γ).obj w)
      (fun w a => PowerWordContentCyclicity.generator D Sc cutoff L (t ++ [i]) γ w a)
      hObj (HEq.refl AG)
    have hWord := eq_of_heq_square he ho hg
    change (ET).hom.total W ((BalancedInduction.moduleMap J F).total W
      (BalancedInduction.unit J (M).toFunctor CS BS)) =
      PowerWordContentCyclicity.generator D Sc cutoff L (t ++ [i]) γ W AG at hr
    exact hr.trans hWord.symm
  have hh := congrArg (fun f => (ES).hom ≫ f) hconj
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh
end OddMath.QuiverHecke.ELVOld.PowerWordContentWhiskering
end

end

section

/-! # Chosen weight crossings in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: transport the given weight crossing through
the selected content pair comparisons, with both colour cases included.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightCross
open CyclotomicAction
universe u
private theorem crossing_paste {C : Type*} [Category* C] {A B E F S T : C}
    (a : A ≅ B) (b : E ≅ F) (s : B ≅ S) (t : F ≅ T)
    (c : B ⟶ F) (w : S ⟶ T) (h : c ≫ t.hom = s.hom ≫ w) :
    ((a.hom ≫ c) ≫ b.inv) ≫ (b ≪≫ t).hom = (a ≪≫ s).hom ≫ w := by
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The existing whole append comparison at equal presentations of its weights. -/
def appendIsoAtWeights (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).obj
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) ≅
        PowerWordWeight.wordFamily D Sc cutoff L Λ y (ν ++ [i]) := by
  cases hx
  cases hy
  exact PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i

omit [Fintype I] in
private theorem next_weight (Λ : X) (ν : List I) (i : I) {x y : X}
    (hx : x = PowerWordWeight.wordWeight D Λ ν) (h : x + D.α i = y) :
    y = PowerWordWeight.wordWeight D Λ (ν ++ [i]) :=
  h.symm.trans ((congrArg (fun z => z + D.α i) hx).trans
    (PowerWordWeight.wordWeight_append D Λ ν i))

section Supported
variable (ν : List I) (i j : I) (Λ : X) {x₀ xj xu xi : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
  (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (hν : (ν : Multiset I) = β.1)

/-- The given supported weight-pair chart followed by the recursively selected
single-append word charts, through the actual first successor block. -/
def pairComponentIso :
    ((elvEFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂ ε).toFunctor).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν)) ≅
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) ε.1 :=
  (eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i j Λ h₁ h₂ β ε hε)).app (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ≪≫
      PowerWordContentCross.pairIsoTo D Sc cutoff L ν i j β.1
        (blockSucc D Λ j h₁ β).1 ε.1 hν
        (elvBlockSucc_content_eq D j Λ h₁ β)
        (elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε)

variable (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The given weight crossing on its occupied pair component is the full signed
old-Hom word crossing. No comparison of operators is assumed. -/
theorem weight_cross_component :
    elvWeightCrossComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ε ≫
        (pairComponentIso D Sc cutoff L ν j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε) hν).hom =
    (pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν).hom ≫
      PowerWordContentCross.wordCross D Sc cutoff L ε.1 ν i j := by
  rw [elvWeightCrossComponent_of D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j)
    (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) β ε hε]
  rw [elvWeightCrossVia_normalized_rectangular D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i j Λ h₁ h₂ β ε hε h₃ h₄]
  have hc := PowerWordContentCross.selected_pair_cross D Sc cutoff L ν β.1 hν i j
    (blockSucc D Λ j h₁ β).1 (blockSucc D Λ i h₃ β).1 ε.1
    (elvBlockSucc_content_eq D j Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₃ β)
    (elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε)
    (elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
  exact crossing_paste
    ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i j Λ h₁ h₂ β ε hε)).app (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν))
    ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      j i Λ h₃ h₄ β ε (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))).app
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν))
    (PowerWordContentCross.pairIsoTo D Sc cutoff L ν i j β.1
      (blockSucc D Λ j h₁ β).1 ε.1 hν
      (elvBlockSucc_content_eq D j Λ h₁ β)
      (elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε))
    (PowerWordContentCross.pairIsoTo D Sc cutoff L ν j i β.1
      (blockSucc D Λ i h₃ β).1 ε.1 hν
      (elvBlockSucc_content_eq D i Λ h₃ β)
      (elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))) _ _ hc
end Supported

/-- The recursive whole-family append comparison, used also to retain all
zero content components of a pair. -/
def recursivePairIso (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
    (hx : x₀ = PowerWordWeight.wordWeight D Λ ν)
    (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).obj
      ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν)) ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) :=
  (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).toFunctor.mapIso
    (appendIsoAtWeights D Sc cutoff L Λ ν j x₀ xj hx (next_weight D Λ ν j hx h₁) h₁) ≪≫
      appendIsoAtWeights D Sc cutoff L Λ (ν ++ [j]) i xj xu
        (next_weight D Λ ν j hx h₁)
        (next_weight D Λ (ν ++ [j]) i (next_weight D Λ ν j hx h₁) h₂) h₂

section Family
variable (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (hν : (ν : Multiset I) = β.1)
omit [Fintype I] in
private theorem initial_weight (β₀ : WeightBlocks D Λ x₀) (h₀ : (ν : Multiset I) = β₀.1) :
    x₀ = PowerWordWeight.wordWeight D Λ ν := by
  exact (congrArg (blockWeight D Λ) h₀).trans β₀.property |>.symm

/-- The selected chart at the occupied output; on other components it uses
the recursive whole-family append charts. -/
def pairFamilyIso :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).obj
      ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν)) ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) := by
  classical
  apply Pi.isoMk
  intro ε
  by_cases hε : blockSucc₂ D i j Λ h₁ h₂ β = ε
  · exact pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν
  · exact Pi.isoApp (recursivePairIso D Sc cutoff L Λ ν i j
      (initial_weight D Λ ν β hν) h₁ h₂) ε

include hν in
/-- Every nonoccupied component of the given double-E source is zero. -/
theorem pair_source_isZero (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β ≠ ε) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).obj
      ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν))) ε) := by
  have hc : ε.1 ≠ (((ν ++ [j]) ++ [i] : List I) : Multiset I) := by
    intro he
    apply hε
    apply Subtype.ext
    change ({i} : Multiset I) + ({j} + β.1) = ε.1
    rw [he, ← hν, ← Multiset.coe_add, ← Multiset.coe_add]
    ac_rfl
  exact (PowerWordWeight.wordAt_isZero D Sc cutoff L ((ν ++ [j]) ++ [i]) ε.1 hc).of_iso
    (Pi.isoApp (recursivePairIso D Sc cutoff L Λ ν i j
      (initial_weight D Λ ν β hν) h₁ h₂) ε)
/-- The chart at every occupied pair block is the given supported chart. -/
theorem pairFamilyIso_hom_of (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom ε =
      (pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν).hom := by
  unfold pairFamilyIso
  simp only [Pi.isoMk_hom, dite_eq_left hε]

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The signed old-Hom crossing on every component of the same word family. -/
def wordFamilyCross :
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) ⟶
      PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [i]) ++ [j]) :=
  fun ε => PowerWordContentCross.wordCross D Sc cutoff L ε.1 ν i j

/-- The chosen weight crossing agrees with the signed old-Hom operator on
all content components, including absent and off-support predecessors. -/
theorem weight_pair_cross :
    (elvActionCross D Sc cutoff (PowerWordContent.powerBound D cutoff L) i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ≫
        (pairFamilyIso D Sc cutoff L Λ ν j i h₃ h₄ β hν).hom =
    (pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom ≫
      wordFamilyCross D Sc cutoff L Λ ν i j (xu := xu) := by
  funext ε
  change elvWeightCrossComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i j Λ
    h₁ h₂ h₃ h₄ (D.parity i * D.parity j) (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ε ≫
      (pairFamilyIso D Sc cutoff L Λ ν j i h₃ h₄ β hν).hom ε =
    (pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom ε ≫
      PowerWordContentCross.wordCross D Sc cutoff L ε.1 ν i j
  classical
  by_cases hε : blockSucc₂ D i j Λ h₁ h₂ β = ε
  · rw [pairFamilyIso_hom_of D Sc cutoff L Λ ν j i h₃ h₄ β hν ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε),
      pairFamilyIso_hom_of D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε]
    exact weight_cross_component D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν h₃ h₄
  · exact (pair_source_isZero D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε).eq_of_src _ _
end Family

end OddMath.QuiverHecke.ELVOld.PowerWordWeightCross
end

end

section

/-! # Arbitrary-arrow append transport on the weight word family

SwappedVacuumCoordinates §§4–6: preserve the existing whole append chart
while transporting arbitrary full old-Hom maps through the chosen E functor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightWhiskering
open CyclotomicAction CyclotomicCrossingTensor
universe u
private theorem square_paste {C : Type*} [Category* C] {A B E F S T : C}
    (ha : A = B) (hb : E = F) (s : B ≅ S) (t : F ≅ T)
    (c : B ⟶ F) (w : S ⟶ T) (h : c ≫ t.hom = s.hom ≫ w) :
    (eqToHom ha ≫ c ≫ eqToHom hb.symm) ≫ (eqToHom hb ≫ t.hom) =
      (eqToHom ha ≫ s.hom) ≫ w := by
  cases ha
  cases hb
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The existing whole append chart at its given supported block. -/
theorem append_component (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (hν : (ν : Multiset I) = β.1) :
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x y hx hy h).hom
      (blockSucc D Λ i h β) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν)) ≫
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β.1 (blockSucc D Λ i h β).1 hν
        (elvBlockSucc_content_eq D i Λ h β)).hom := by
  cases hx
  cases hy
  have hβ : β = PowerWordWeight.wordBlock D Λ ν := Subtype.ext hν.symm
  subst β
  change (PowerWordWeight.weightAppendAtIso D Sc cutoff L Λ ν i
    (blockSucc D Λ i h (PowerWordWeight.wordBlock D Λ ν))).hom = _
  unfold PowerWordWeight.weightAppendAtIso
  simp only
  rfl

/-- The full signed old-Hom map on every unchanged content component. -/
def wordFamilyArrow (Λ x : X) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordWeight.wordFamily D Sc cutoff L Λ x s ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ x t :=
  fun β => PowerWordContentCross.contentWordArrow D Sc cutoff L β.1 s t g

/-- The single-E source vanishes outside the content of the appended word. -/
theorem append_source_isZero (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y)
    (δ : WeightBlocks D Λ y) (hδ : δ.1 ≠ (((ν ++ [i]) : List I) : Multiset I)) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).obj
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν)) δ) :=
  (PowerWordWeight.wordAt_isZero D Sc cutoff L (ν ++ [i]) δ.1 hδ).of_iso
    (Pi.isoApp (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x y hx hy h) δ)

/-- The given E functor intertwines arbitrary full old-Hom maps through the
existing whole single-append charts, on every content component. -/
theorem append_family_arrow (Λ : X) (s t : List I) (i : I) (x y : X)
    (hxs : x = PowerWordWeight.wordWeight D Λ s)
    (hys : y = PowerWordWeight.wordWeight D Λ (s ++ [i]))
    (hxt : x = PowerWordWeight.wordWeight D Λ t)
    (hyt : y = PowerWordWeight.wordWeight D Λ (t ++ [i]))
    (h : x + D.α i = y) (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).map
      (wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x y hxt hyt h).hom =
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x y hxs hys h).hom ≫
      wordFamilyArrow D Sc cutoff L Λ y (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g) := by
  funext δ
  let β : WeightBlocks D Λ x := ⟨s, hxs.symm⟩
  classical
  by_cases he : δ = blockSucc D Λ i h β
  · subst δ
    change (elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h
      (blockSucc D Λ i h β)).map (wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x y hxt hyt h).hom
          (blockSucc D Λ i h β) =
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x y hxs hys h).hom
          (blockSucc D Λ i h β) ≫
        PowerWordContentCross.contentWordArrow D Sc cutoff L (blockSucc D Λ i h β).1
          (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g)
    rw [append_component D Sc cutoff L Λ t i x y hxt hyt h β hst.symm,
      append_component D Sc cutoff L Λ s i x y hxs hys h β rfl,
      elvInductionComponent_map_blockSucc]
    have hc := PowerWordContentWhiskering.append_word_arrow D Sc cutoff L s t i β.1
      (blockSucc D Λ i h β).1 rfl hst.symm (elvBlockSucc_content_eq D i Λ h β) g
    have hp := square_paste
      (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x s))
      (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x t))
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L s i β.1 (blockSucc D Λ i h β).1 rfl
        (elvBlockSucc_content_eq D i Λ h β))
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L t i β.1 (blockSucc D Λ i h β).1 hst.symm
        (elvBlockSucc_content_eq D i Λ h β)) _ _ hc
    dsimp only [elvBlockInd, elvBlockAppend, wordFamilyArrow, Superfunctor.map]
    simpa only [Category.assoc] using hp
  · have hd : δ.1 ≠ (((s ++ [i]) : List I) : Multiset I) := by
      intro hd
      apply he
      apply Subtype.ext
      change δ.1 = {i} + (s : Multiset I)
      rw [hd, ← Multiset.coe_add]
      exact add_comm _ _
    exact (append_source_isZero D Sc cutoff L Λ s i x y hxs hys h δ hd).eq_of_src _ _

end OddMath.QuiverHecke.ELVOld.PowerWordWeightWhiskering
end

end

section

/-! # Recursive pair charts for the weight word family

SwappedVacuumCoordinates §§4–6: the supported crossing chart must agree
with the unchanged recursively selected whole single-append comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordPairCoherence
open CyclotomicAction CyclotomicCrossingTensor
universe u
private theorem chart_join {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {X₀ X₁ Y : C} {A Z W : B}
    (h₀ : A = F.obj X₀) (h₁ : X₀ = X₁) (h₂ : A = F.obj X₁) (h₃ : Z = F.obj Y)
    (e : X₁ ≅ Y) (f : F.obj Y ≅ W) :
    (eqToHom h₀ ≫ F.map (eqToHom h₁ ≫ e.hom) ≫ eqToHom h₃.symm) ≫
      (eqToHom h₃ ≫ f.hom) = eqToHom h₂ ≫ F.map e.hom ≫ f.hom := by
  cases h₁
  cases h₀
  cases h₃
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
  (hx : x₀ = PowerWordWeight.wordWeight D Λ ν)
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (hν : (ν : Multiset I) = (Subtype.val β))
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "M" => PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν
local notation "BJ" => blockSucc D Λ j h₁ β
local notation "BU" => blockSucc₂ D i j Λ h₁ h₂ β
local notation "K" => elvBlockInd D Sc cutoff N j Λ h₁ β
local notation "U" => elvBlockInd D Sc cutoff N i Λ h₂ BJ
local notation "HK" => elvBlockSucc_content_eq D j Λ h₁ β
local notation "HU" => elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β BU rfl
local notation "EK" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j (Subtype.val β) (Subtype.val BJ) hν HK
local notation "EU" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L (ν ++ [j]) i (Subtype.val BJ) (Subtype.val BU)
  (PowerWordContentCross.appendContentEq ν j (Subtype.val β) (Subtype.val BJ) hν HK) HU

/-- The recursively chosen whole pair chart agrees on its occupied component
with the existing rectangular chart and the recursively chosen content chart. -/
theorem recursive_pair_component :
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom BU =
      (PowerWordWeightCross.pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β BU rfl hν).hom := by
  have hxj : xj = PowerWordWeight.wordWeight D Λ (ν ++ [j]) :=
    h₁.symm.trans ((congrArg (fun x => x + D.α j) hx).trans
      (PowerWordWeight.wordWeight_append D Λ ν j))
  have hxu : xu = PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
    h₂.symm.trans ((congrArg (fun x => x + D.α i) hxj).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
  change (elvInductionComponent D Sc cutoff N i Λ h₂ BU).map
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν j x₀ xj hx hxj h₁).hom ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ (ν ++ [j]) i xj xu hxj hxu h₂).hom BU = _
  rw [elvInductionComponent_map_blockSucc D Sc cutoff N i Λ h₂ BJ,
    PowerWordWeightWhiskering.append_component D Sc cutoff L Λ ν j x₀ xj hx hxj h₁ β hν,
    PowerWordWeightWhiskering.append_component D Sc cutoff L Λ (ν ++ [j]) i xj xu hxj hxu h₂ BJ
      (PowerWordContentCross.appendContentEq ν j (Subtype.val β) (Subtype.val BJ) hν HK)]
  have hp := chart_join (U).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ BJ
      ((elvE D Sc cutoff N j Λ h₁).obj M))
    (elvInductionComponent_obj_blockSucc D Sc cutoff N j Λ h₁ β M)
    (Functor.congr_obj (elvEFunctor_comp₂_rectangular_eq D Sc cutoff N i j Λ h₁ h₂ β BU rfl) M)
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ BJ
      (PowerWordWeight.wordFamily D Sc cutoff L Λ xj (ν ++ [j]))) EK EU
  dsimp only [elvBlockInd, elvBlockAppend, PowerWordWeight.wordFamily, Superfunctor.map] at hp ⊢
  simpa only [PowerWordWeightCross.pairComponentIso, PowerWordContentCross.pairIsoTo,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom, eqToHom_app,
    Category.assoc] using hp

/-- The supported crossing chart has exactly the same whole hom as the
unchanged recursive single-append chart, including every zero component. -/
theorem recursive_pair_hom :
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom =
      (PowerWordWeightCross.pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom := by
  funext ε
  classical
  by_cases hε : BU = ε
  · subst ε
    rw [PowerWordWeightCross.pairFamilyIso_hom_of D Sc cutoff L Λ ν i j h₁ h₂ β hν BU rfl]
    exact recursive_pair_component D Sc cutoff L Λ ν i j hx h₁ h₂ β hν
  · exact (PowerWordWeightCross.pair_source_isZero D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε).eq_of_src _ _

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The given whole weight crossing in the unchanged recursively selected
word charts, for both colour cases and all exterior coefficient vectors. -/
theorem recursive_pair_cross :
    (elvActionCross D Sc cutoff N i j Λ h₁ h₂ h₃ h₄).app (D.parity i * D.parity j) M ≫
      (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν j i hx h₃ h₄).hom =
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L Λ ν i j (xu := xu) := by
  let β₀ : WeightBlocks D Λ x₀ := ⟨ν, hx.symm⟩
  rw [recursive_pair_hom D Sc cutoff L Λ ν j i hx h₃ h₄ β₀ rfl,
    recursive_pair_hom D Sc cutoff L Λ ν i j hx h₁ h₂ β₀ rfl]
  exact PowerWordWeightCross.weight_pair_cross D Sc cutoff L Λ ν i j h₁ h₂ β₀ rfl h₃ h₄
end OddMath.QuiverHecke.ELVOld.PowerWordPairCoherence
end

end

section

/-! # Evenness of the selected word charts

SwappedVacuumCoordinates §§4–6: unit evaluation and cyclicity detect the
parity of the existing word comparisons before odd generator transport.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordChartParity
open CyclotomicAction
universe u
section Generic
variable {k C B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
private theorem even_comp {E : Type*} [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    {A Z W : E} {f : A ⟶ Z} {g : Z ⟶ W}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) :
    f ≫ g ∈ parity (R := k) _ _ 0 := by
  simpa only [zero_add] using comp_mem hf hg

private theorem eq_to_hom_even {E : Type*} [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    {A Z : E} (h : A = Z) : eqToHom h ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem _

private theorem even_of_eval {M N : Superfunctor k C (SVec k)} (s : C) (b : M.obj s)
    (H : Function.Injective (fun f : M ⟶ N => f.total s b))
    (hb : b ∈ (M.obj s).part 0) (f : M ⟶ N) (hf : f.total s b ∈ (N.obj s).part 0) :
    f ∈ parity (R := k) _ _ 0 := by
  have h1 := (PowerWordContentCross.even_unit_components f s b (f.total s b) hb hf rfl).2
  have hp : proj k 1 f = 0 := by
    apply H
    simp only [SuperNatTrans.total, Superfunctor.proj_app, Superfunctor.zero_app,
      show (0 : ZMod 2) ≠ 1 from by decide, ite_false, ite_true, zero_add, h1]
    rfl
  have hs : proj k 0 f + proj k 1 f = f := proj_add_proj f
  rw [hp, add_zero] at hs
  rw [← hs]
  exact proj_mem 0 f

variable (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
private theorem adjunction_evaluate (M : Superfunctor k C (SVec k))
    (N : Superfunctor k B (SVec k)) (s : C) (b : M.obj s)
    (f : BalancedInduction.induced J M ⟶ N) :
    ((BalancedInduction.adjunction J).homEquiv M N f).total s b =
      f.total (J.obj s) (BalancedInduction.unit J M.toFunctor s b) := by
  rw [Adjunction.homEquiv_unit, Superfunctor.comp_total, SVec.comp_apply]
  change ((BalancedInduction.restriction J).map f).total s
    (((BalancedInduction.adjunctionUnit J).app M).total s b) = _
  rw [BalancedInduction.unit_total_apply]
  rfl

private theorem induction_eval_injective (M : Superfunctor k C (SVec k))
    (N : Superfunctor k B (SVec k)) (s : C) (b : M.obj s)
    (H : Function.Injective (fun f : M ⟶ (BalancedInduction.restriction J).obj N => f.total s b)) :
    Function.Injective (fun f : BalancedInduction.induced J M ⟶ N =>
      f.total (J.obj s) (BalancedInduction.unit J M.toFunctor s b)) := by
  intro f g h
  apply ((BalancedInduction.adjunction J).homEquiv M N).injective
  apply H
  change ((BalancedInduction.adjunction J).homEquiv M N f).total s b =
    ((BalancedInduction.adjunction J).homEquiv M N g).total s b
  exact (adjunction_evaluate J M N s b f).trans (h.trans (adjunction_evaluate J M N s b g).symm)
private theorem unit_even (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s)
    (hb : b ∈ (M.obj s).part 0) :
    (show (BalancedInduction.induced J M).obj (J.obj s) from
      BalancedInduction.unit J M.toFunctor s b) ∈
      ((BalancedInduction.induced J M).obj (J.obj s)).part 0 := by
  change BalancedInduction.unit J M.toFunctor s b ∈
    (BalancedInduction.superspace J M.toFunctor (J.obj s)).part 0
  simpa only [zero_add] using SVec.apply_mem_part (BalancedInduction.unit_mem J M s) hb

end Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I) (β γ : Multiset I)
  (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hi
local notation "M" => PowerWordWeight.wordAt D Sc cutoff L ν β
local notation "P" => PowerWordWeight.wordAt D Sc cutoff L (ν ++ [i]) γ
local notation "S" => PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν
local notation "B" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν
local notation "W" => CategoryTheory.Functor.obj J S
local notation "HI" => PowerWordContentCross.appendContentEq ν i β γ hν hi
local notation "E" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi

/-- The given exact-content append comparison is even at every valid content
presentation, detected from its unit image and the cyclic source adjunction. -/
theorem content_append_to_even :
    (E).hom ∈ parity (R := k) _ _ 0 := by
  have H : Function.Injective (fun f : BalancedInduction.induced J M ⟶ P =>
      f.total W (BalancedInduction.unit J (M).toFunctor S B)) := by
    apply induction_eval_injective
    intro f g h
    exact PowerWordContentCyclicity.hom_ext D Sc cutoff L ν β hν
      ((BalancedInduction.restriction J).obj P) f g h
  apply even_of_eval W (BalancedInduction.unit J (M).toFunctor S B) H
  · exact unit_even J M S B (PowerWordContentCyclicity.wordUnit_even D Sc cutoff L ν β hν)
  · rw [PowerWordContentCross.append_unit_to D Sc cutoff L ν i β γ hν hi]
    exact PowerWordContentCyclicity.wordUnit_even D Sc cutoff L (ν ++ [i]) γ HI

/-- The existing whole single-append weight chart is even on all components. -/
theorem weight_append_even (Λ : X) :
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom ∈ parity (R := k) _ _ 0 := by
  intro δ
  classical
  by_cases hδ : δ = blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i)
      (PowerWordWeight.wordBlock D Λ ν)
  · subst δ
    change (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i _ _ rfl rfl
      (PowerWordWeight.wordWeight_append D Λ ν i)).hom _ ∈ _
    rw [PowerWordWeightWhiskering.append_component D Sc cutoff L Λ ν i _ _ rfl rfl
      (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν) rfl]
    exact even_comp (eq_to_hom_even _) (content_append_to_even D Sc cutoff L ν i _ _ rfl
      (elvBlockSucc_content_eq D i Λ (PowerWordWeight.wordWeight_append D Λ ν i)
        (PowerWordWeight.wordBlock D Λ ν)))
  · have hz : (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom δ = 0 :=
      (PowerWordWeight.weightAppend_isZero D Sc cutoff L Λ ν i δ hδ).eq_of_src _ _
    rw [hz]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELVOld.PowerWordChartParity
end

end

section

/-! # The chosen original-weight dot in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: identify the existing original-weight dot
on every actual word-family E component through its selected comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightDot
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The same descended old-Hom dot on any exact-content component. -/
def wordDotAt (ν : List I) (i : I) (β : Multiset I) : End (PowerWordWeight.wordAt D Sc cutoff L (ν ++ [i]) β) :=
  (BalancedInduction.restriction
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)).map
      (PowerWordContentDot.weightedWordDot D Sc cutoff L ν i)

private theorem contentDotTo_square (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hγ : β + ([i] : Multiset I) = γ) :
    (contentInductionTransform D Sc cutoff (PowerWordContent.powerBound D cutoff L) hγ hγ (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)).app (D.parity i)
        (PowerWordWeight.wordAt D Sc cutoff L ν β) ≫
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hγ).hom =
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hγ).hom ≫ wordDotAt D Sc cutoff L ν i γ := by
  subst β
  have he : γ = ((ν ++ [i] : List I) : Multiset I) := hγ.symm.trans (Multiset.coe_add ν [i])
  subst γ
  have hc := PowerWordContentDot.content_append_dot D Sc cutoff L ν i
  rw [PowerWordContentDot.chosenContentDot_eq] at hc
  exact hc

private theorem conjugate_from_eq {C : Type*} [Category* C] {A B E : C}
    (e : A ≅ B) (f : B ≅ E) (s : A ⟶ A) (x : B ⟶ B) (y : E ⟶ E)
    (hs : s = e.hom ≫ x ≫ e.inv) (h : x ≫ f.hom = f.hom ≫ y) :
    s ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ y := by
  rw [hs]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The actual weight dot at the occupied successor block is the literal
old-Hom word dot under the prescribed original-weight comparison. -/
theorem weight_dot_component (Λ : X) (ν : List I) (i : I) :
    elvWeightDotComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i) (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)
      (blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)) ≫
        (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν i).hom =
    (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν i).hom ≫
      wordDotAt D Sc cutoff L ν i
        (blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)).1 :=
  conjugate_from_eq
    (eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)))
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i _ _ rfl (by rw [blockSucc_val, add_comm]; rfl))
    _ _ _
    (elvWeightDotComponent_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i) (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)
      (PowerWordWeight.wordBlock D Λ ν))
    (contentDotTo_square D Sc cutoff L ν i _ _ rfl (by rw [blockSucc_val, add_comm]; rfl))

/-- The full old-Hom dot on every block of the next word family. -/
def wordFamilyDot (Λ : X) (ν : List I) (i : I) :
    End (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [i])) (ν ++ [i])) :=
  fun δ => wordDotAt D Sc cutoff L ν i δ.1

private theorem selected_hom (Λ : X) (ν : List I) (i : I) :
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom
      (blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)) =
      (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν i).hom := by
  change (PowerWordWeight.weightAppendAtIso D Sc cutoff L Λ ν i _).hom = _
  unfold PowerWordWeight.weightAppendAtIso
  simp

/-- The independently chosen original-weight dot is the full old-Hom word
dot under the selected whole-family comparison. Every present and absent
content component is included, and no operator-comparison premise is used. -/
theorem weight_append_dot (Λ : X) (ν : List I) (i : I) :
    (elvActionDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i)).app (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν) ≫
        (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom =
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom ≫ wordFamilyDot D Sc cutoff L Λ ν i := by
  funext δ
  change elvWeightDotComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i) (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν) δ ≫
        (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom δ =
      (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom δ ≫ wordDotAt D Sc cutoff L ν i δ.1
  classical
  by_cases hδ : δ = blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)
  · subst δ
    rw [selected_hom]
    exact weight_dot_component D Sc cutoff L Λ ν i
  · exact (PowerWordWeight.weightAppend_isZero D Sc cutoff L Λ ν i δ hδ).eq_of_src _ _

end OddMath.QuiverHecke.ELVOld.PowerWordWeightDot
end

end

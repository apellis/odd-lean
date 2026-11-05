import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordPairCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionTensor

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

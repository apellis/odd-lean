import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentCross
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMateComparison

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

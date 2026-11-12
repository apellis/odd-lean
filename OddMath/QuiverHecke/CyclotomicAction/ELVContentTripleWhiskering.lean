/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations

/-! # Whiskering of crossings on three content induction functors -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K K' : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
variable (L L' : C ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  [L'.Additive] [L'.Linear k] [IsSuperfunctor k L']

/-- Outer whiskering with independently recast source and target functors. -/
theorem compForward_outer_arrow_recast (e : J ⋙ K = L) (e' : J ⋙ K' = L')
    {p : ZMod 2} {a : ∀ w, K.obj w ⟶ K'.obj w} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L'.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (a (J.obj v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    (moduleIsoLinearEquiv ((inductionCompOfEq J K L e).app M) z).toLinearMap ∘ₗ
        transformLinear ha (induced J M) z =
      transformLinear hb M z ∘ₗ
        (moduleIsoLinearEquiv ((inductionCompOfEq J K' L' e').app M) z).toLinearMap := by
  subst L
  subst L'
  have hab' : (fun v => a (J.obj v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_outer J ha M z
/-- Recast both ends of inner whiskering without identifying the append words. -/
theorem compForward_inner_arrow_recast
    (J' : C ⥤ D) [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
    (e : J ⋙ K = L) (e' : J' ⋙ K = L')
    {p : ZMod 2} {a : ∀ v, J.obj v ⟶ J'.obj v} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L'.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (K.map (a v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    (moduleIsoLinearEquiv ((inductionCompOfEq J K L e).app M) z).toLinearMap ∘ₗ
        mapComponent K (transformComponent ha M) p z =
      transformLinear hb M z ∘ₗ
        (moduleIsoLinearEquiv ((inductionCompOfEq J' K L' e').app M) z).toLinearMap := by
  subst L
  subst L'
  have hab' : (fun v => K.map (a v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_inner K ha M z
end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
open MonoidalCategory
open scoped TensorProduct
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem arrowRecast_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

theorem appendComponent_leftContext_arrow_heq (v σ τ τ' : List I)
    (a : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D τ')) :
    HEq (truncatedAppendComponent D Sc cutoff N a ⟨v ++ σ⟩)
      (truncatedAppendComponent D Sc cutoff N
        ((pres D Sc).obj (ob D σ) ◁ a) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) (𝟙 ((pres D Sc).obj (ob D σ))) a
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq ((pres D Sc).obj (ob D (v ++ σ)) ◁ a)
      ((pres D Sc).obj (ob D v) ◁ ((pres D Sc).obj (ob D σ) ◁ a)) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ'))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact arrowRecast_map_heq
    (i := ((v ++ σ) ++ τ, (v ++ σ) ++ τ')) (j := (v ++ (σ ++ τ), v ++ (σ ++ τ')))
    (A := fun w : List I × List I => (pres D Sc).obj (ob D w.1) ⟶ (pres D Sc).obj (ob D w.2))
    (B := fun w : List I × List I => TruncatedOld D Sc cutoff N w.1 w.2)
    (fun w f => (truncatedIdeal D Sc cutoff N w.1 w.2).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (Prod.ext (List.append_assoc v σ τ) (List.append_assoc v σ τ')) hh

/-- Nonendomorphism outer source comparison, retaining both endpoint casts. -/
theorem contentInductionComp_outer_arrow (β : Multiset I) (σ τ τ' : List I)
    (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (ht : (β + (σ : Multiset I)) + (τ' : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (ht' : β + ((σ ++ τ' : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D τ')}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h ht ha)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ _ rfl) M) z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' ht'
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ' γ ht ht').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_outer_arrow_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ' γ ht)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppendTo D Sc cutoff N β (σ ++ τ') γ ht')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ' γ ht ht')
    (contentAppendTo_supernatural D Sc cutoff N h ht ha)
    (contentAppendTo_supernatural D Sc cutoff N h' ht'
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha))
    (fun v => appendComponent_leftContext_arrow_heq D Sc cutoff N v.obj.word σ τ τ' a) M z

theorem appendComponent_rightContext_arrow_heq (v σ σ' τ : List I)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (v ++ σ')
      (truncatedAppendComponent D Sc cutoff N a ⟨v⟩))
      (truncatedAppendComponent D Sc cutoff N
        (a ▷ (pres D Sc).obj (ob D τ)) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) a (𝟙 ((pres D Sc).obj (ob D τ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq (((pres D Sc).obj (ob D v) ◁ a) ▷ (pres D Sc).obj (ob D τ))
      ((pres D Sc).obj (ob D v) ◁ (a ▷ (pres D Sc).obj (ob D τ))) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ' τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact arrowRecast_map_heq
    (i := ((v ++ σ) ++ τ, (v ++ σ') ++ τ)) (j := (v ++ (σ ++ τ), v ++ (σ' ++ τ)))
    (A := fun w : List I × List I => (pres D Sc).obj (ob D w.1) ⟶ (pres D Sc).obj (ob D w.2))
    (B := fun w : List I × List I => TruncatedOld D Sc cutoff N w.1 w.2)
    (fun w f => (truncatedIdeal D Sc cutoff N w.1 w.2).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (Prod.ext (List.append_assoc v σ τ) (List.append_assoc v σ' τ)) hh

/-- Inner nonendomorphism whiskering at an explicit common intermediate content. -/
theorem contentInductionCompTo_inner_arrow (β : Multiset I) (σ σ' : List I)
    (δ : Multiset I) (hδ : β + (σ : Multiset I) = δ) (hδ' : β + (σ' : Multiset I) = δ)
    (τ : List I) (γ : Multiset I) (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (h' : β + ((σ' ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h).app M) z).toLinearMap ∘ₗ
      BalancedInduction.mapComponent (contentAppendTo D Sc cutoff N δ τ γ hγ)
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N hδ hδ' ha) M) p z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h h'
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h').app M) z).toLinearMap := by
  rw [contentInductionCompTo_eq, contentInductionCompTo_eq]
  exact BalancedInduction.compForward_inner_arrow_recast
    (contentAppendTo D Sc cutoff N β σ δ hδ)
    (contentAppendTo D Sc cutoff N δ τ γ hγ)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h)
    (contentAppendTo D Sc cutoff N β (σ' ++ τ) γ h')
    (contentAppendTo D Sc cutoff N β σ' δ hδ')
    (contentAppend_compTo_eq D Sc cutoff N β σ δ hδ τ γ hγ h)
    (contentAppend_compTo_eq D Sc cutoff N β σ' δ hδ' τ γ hγ h')
    (contentAppendTo_supernatural D Sc cutoff N hδ hδ' ha)
    (contentAppendTo_supernatural D Sc cutoff N h h'
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha))
    (fun v => appendComponent_rightContext_arrow_heq D Sc cutoff N v.obj.word σ σ' τ a) M z

private def compIsoApp {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E) (e : J ⋙ K ≅ L) (M : C) :
    K.obj (J.obj M) ≅ L.obj M := e.app M

private theorem compIsoApp_hom_mem
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E) (e : J ⋙ K ≅ L) (M : C)
    {p : ZMod 2} (he : e.hom.app M ∈ parity (R := k) _ _ p) :
    (compIsoApp J K L e M).hom ∈ parity (R := k) _ _ p := he

private theorem total_of_mem
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

private theorem map_transform_total
    {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {F G : Superfunctor k C (SVec k)} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : B) :
    ((BalancedInduction.induction J).map f).total z = BalancedInduction.mapComponent J f p z :=
  total_of_mem (Supercategory.map_mem (BalancedInduction.induction J) hf) z

theorem contentTripleLeft_whisker (i j l : I) :
    contentTripleLeft D Sc i j l = crossTwo D Sc i j ▷ (pres D Sc).obj (ob D [l]) := by
  rw [crossTwo, cl_whiskerRight D Sc _ _ [l]
    (by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp [PG.pos, PG.width])]
  rfl

/-- The normalized prefix source on the canonical three-letter objects. -/
def contentTriplePrefixAffine (i j l : I) :
    (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [j,i,l]) := by
  classical
  exact if i = j then -contentTripleLeft D Sc i j l else contentTripleLeft D Sc i j l

theorem contentTriplePrefixAffine_mem (i j l : I) :
    contentTriplePrefixAffine D Sc i j l ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  classical
  unfold contentTriplePrefixAffine
  split_ifs
  · exact Submodule.neg_mem _ (contentTripleLeft_parity D Sc i j l)
  · exact contentTripleLeft_parity D Sc i j l

theorem contentTriplePrefixAffine_eq_whisker (i j l : I) :
    contentTriplePrefixAffine D Sc i j l =
      contentCrossAffine D Sc i j ▷ (pres D Sc).obj (ob D [l]) := by
  classical
  by_cases hij : i = j
  · simp only [contentTriplePrefixAffine, contentCrossAffine, ite_eq_left hij,
      MonoidalSupercategory.neg_whiskerRight (R := k), contentTripleLeft_whisker]
  · simp only [contentTriplePrefixAffine, contentCrossAffine, ite_eq_right hij,
      contentTripleLeft_whisker]

private theorem homogeneous_total_ext
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f g : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p)
    (h : ∀ z, f.total z = g.total z) : f = g := by
  apply SuperNatTrans.ext
  funext q z
  by_cases hq : q = p
  · subst q
    rw [← total_of_mem hf, ← total_of_mem hg]
    exact h z
  · rw [Superfunctor.app_eq_zero_of_mem hf hq,
      Superfunctor.app_eq_zero_of_mem hg hq]

private theorem contentInductionTransform_app
    {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) (M : ContentModules D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N hσ hτ ha).app p M =
      BalancedInduction.transformComponent (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M :=
  congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha))) M

/-- Inner-arrow comparison before evaluating the target module. -/
theorem contentInductionCompTo_inner_map (β : Multiset I) (σ σ' : List I)
    (δ : Multiset I) (hδ : β + (σ : Multiset I) = δ) (hδ' : β + (σ' : Multiset I) = δ)
    (τ : List I) (γ : Multiset I) (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (h' : β + ((σ' ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')}
    (ha : a ∈ parity (R := k) _ _ p) (M : ContentModules D Sc cutoff N β) :
    (contentInductionTo D Sc cutoff N δ τ γ hγ).map
        ((contentInductionTransform D Sc cutoff N hδ hδ' ha).app p M) ≫
      (compIsoApp
      (contentInductionTo D Sc cutoff N β σ δ hδ)
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h)
      (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M).hom =
    (compIsoApp
      (contentInductionTo D Sc cutoff N β σ' δ hδ')
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ' ++ τ) γ h')
      (contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h') M).hom ≫
      (contentInductionTransform D Sc cutoff N h h'
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)).app p M := by
  have hm := (contentInductionTransform D Sc cutoff N hδ hδ' ha).app_mem p M
  have hc := (contentInductionTransform D Sc cutoff N h h'
    (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)).app_mem p M
  have hf := compIsoApp_hom_mem
    (contentInductionTo D Sc cutoff N β σ δ hδ)
    (contentInductionTo D Sc cutoff N δ τ γ hγ)
    (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h)
    (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M
    (contentInductionCompTo_mem D Sc cutoff N β σ δ hδ τ γ hγ h M).1
  have hf' := compIsoApp_hom_mem
    (contentInductionTo D Sc cutoff N β σ' δ hδ')
    (contentInductionTo D Sc cutoff N δ τ γ hγ)
    (contentInductionTo D Sc cutoff N β (σ' ++ τ) γ h')
    (contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h') M
    (contentInductionCompTo_mem D Sc cutoff N β σ' δ hδ' τ γ hγ h' M).1
  apply homogeneous_total_ext (p := p)
    (by simpa only [add_zero] using
      comp_mem (Supercategory.map_mem (contentInductionTo D Sc cutoff N δ τ γ hγ) hm) hf)
    (by simpa only [zero_add] using comp_mem hf' hc)
  intro z
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  change (moduleIsoLinearEquiv
      ((contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h).app M) z).toLinearMap ∘ₗ
      ((contentInductionTo D Sc cutoff N δ τ γ hγ).map
        ((contentInductionTransform D Sc cutoff N hδ hδ' ha).app p M)).total z =
    ((contentInductionTransform D Sc cutoff N h h'
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)).app p M).total z ∘ₗ
      (moduleIsoLinearEquiv
        ((contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h').app M) z).toLinearMap
  rw [contentInductionTransform_total,
    map_transform_total _ hm, contentInductionTransform_app]
  exact contentInductionCompTo_inner_arrow D Sc cutoff N β σ σ' δ hδ hδ' τ γ hγ h h' ha M z

/-- Intermediate source-arrow form of the module comparison. The equality
identifies the supplied arrow with the same right-whiskered source; the prefix
comparison discharges it with `contentTriplePrefixAffine_eq_whisker`. -/
theorem contentInductionCompTo_inner_map_of_eq (β : Multiset I) (σ σ' : List I)
    (δ : Multiset I) (hδ : β + (σ : Multiset I) = δ) (hδ' : β + (σ' : Multiset I) = δ)
    (τ : List I) (γ : Multiset I) (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (h' : β + ((σ' ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D σ')}
    (ha : a ∈ parity (R := k) _ _ p)
    {b : (pres D Sc).obj (ob D (σ ++ τ)) ⟶ (pres D Sc).obj (ob D (σ' ++ τ))}
    (hb : b ∈ parity (R := k) _ _ p)
    (hab : b = a ▷ (pres D Sc).obj (ob D τ))
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionTo D Sc cutoff N δ τ γ hγ).map
        ((contentInductionTransform D Sc cutoff N hδ hδ' ha).app p M) ≫
      (compIsoApp
      (contentInductionTo D Sc cutoff N β σ δ hδ)
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h)
      (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M).hom =
    (compIsoApp
      (contentInductionTo D Sc cutoff N β σ' δ hδ')
      (contentInductionTo D Sc cutoff N δ τ γ hγ)
      (contentInductionTo D Sc cutoff N β (σ' ++ τ) γ h')
      (contentInductionCompTo D Sc cutoff N β σ' δ hδ' τ γ hγ h') M).hom ≫
      (contentInductionTransform D Sc cutoff N h h' hb).app p M := by
  cases hab
  exact contentInductionCompTo_inner_map D Sc cutoff N β σ σ' δ hδ hδ' τ γ hγ h h' ha M

section PrefixComparisonPremises
variable
  (β : Multiset I) (i j l : I) (δ γ : Multiset I)
  (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
  (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([j,i,l] : Multiset I) = γ)
  (hγ : δ + ([l] : Multiset I) = γ)
  (M : ContentModules D Sc cutoff N β)

end PrefixComparisonPremises

end OddMath.QuiverHecke.ELVOld

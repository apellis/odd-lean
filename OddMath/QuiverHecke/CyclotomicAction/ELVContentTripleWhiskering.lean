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

private theorem moduleIsoLinearEquiv_trans
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {A B E : Superfunctor k C (SVec k)} (e : A ≅ B) (f : B ≅ E) (z : C) :
    moduleIsoLinearEquiv (e ≪≫ f) z =
      (moduleIsoLinearEquiv e z).trans (moduleIsoLinearEquiv f z) := by
  apply LinearEquiv.ext
  intro x
  change ((e.hom ≫ f.hom).total z) x = _
  rw [Superfunctor.comp_total]
  rfl

private theorem suffixIso_linearEquiv
    {C B E : Type*} {T : Type u} [Category* C] [Category* B] [Category* E]
    [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]
    (J : C ⥤ B) (K : B ⥤ E) (L : E ⥤ Superfunctor k T (SVec k))
    (P : B ⥤ Superfunctor k T (SVec k)) (R : C ⥤ Superfunctor k T (SVec k))
    (e : K ⋙ L ≅ P) (f : J ⋙ P ≅ R) (M : C) (z : T) :
    moduleIsoLinearEquiv
      ((Functor.associator J K L ≪≫ Functor.isoWhiskerLeft J e ≪≫ f).app M) z =
      (moduleIsoLinearEquiv (e.app (J.obj M)) z).trans
        (moduleIsoLinearEquiv (f.app M) z) := by
  have he : ((Functor.associator J K L ≪≫ Functor.isoWhiskerLeft J e ≪≫ f).app M) =
      e.app (J.obj M) ≪≫ f.app M := by
    apply Iso.ext
    simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.id_comp]
  rw [he, moduleIsoLinearEquiv_trans]

/-- The whole coherence square factors the triple equivalence through the suffix pair. -/
theorem contentETripleEquiv_suffix (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hs : (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleEquiv D Sc cutoff N β i j l γ h M z =
      (contentEPairEquiv D Sc cutoff N (β + ([i] : Multiset I)) j l γ hs
        (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z).trans
      (moduleIsoLinearEquiv
        ((contentInductionComp D Sc cutoff N β [i] [j,l] γ hs h).app M) z) := by
  unfold contentETripleEquiv
  rw [contentETripleComparison_assoc D Sc cutoff N β i j l γ h hs]
  exact suffixIso_linearEquiv _ _ _ _ _ _ _ M z

private theorem transport_outer_square
    {A B C A' B' C' : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup A'] [Module k A']
    [AddCommGroup B'] [Module k B'] [AddCommGroup C'] [Module k C']
    (e : A ≃ₗ[k] B) (f : B ≃ₗ[k] C) (e' : A' ≃ₗ[k] B') (f' : B' ≃ₗ[k] C')
    (b : B' →ₗ[k] B) (c : C' →ₗ[k] C)
    (h : f.toLinearMap ∘ₗ b = c ∘ₗ f'.toLinearMap) :
    (e.trans f).symm.toLinearMap ∘ₗ c ∘ₗ (e'.trans f').toLinearMap =
      e.symm.toLinearMap ∘ₗ b ∘ₗ e'.toLinearMap := by
  apply LinearMap.ext
  intro x
  change e.symm (f.symm (c (f' (e' x)))) = e.symm (b (e' x))
  apply congrArg e.symm
  apply f.injective
  rw [f.apply_symm_apply]
  exact (congrArg (fun q : B' →ₗ[k] C => q (e' x)) h).symm

/-- The suffix crossing is the pair crossing on the independently induced first letter.
Both swapped endpoint casts and the equal-colour minus normalization are retained. -/
theorem contentETripleMap_suffix_cross (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (ht : β + ([i,l,j] : Multiset I) = γ)
    (hs : (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ)
    (hst : (β + ([i] : Multiset I)) + ([l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h ht
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (contentCrossAffine_mem D Sc j l)) M z =
      contentEPairCross D Sc cutoff N (β + ([i] : Multiset I)) j l γ hs hst
        (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M) z := by
  unfold contentETripleMap
  rw [contentETripleEquiv_suffix D Sc cutoff N β i j l γ h hs,
    contentETripleEquiv_suffix D Sc cutoff N β i l j γ ht hst]
  exact transport_outer_square _ _ _ _ _ _
    (contentInductionComp_outer_arrow D Sc cutoff N β [i] [j,l] [l,j] γ hs hst h ht
      (contentCrossAffine_mem D Sc j l) M z)

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

/-- Changing only the intermediate content is an equality transport of the iterated functor. -/
theorem contentETripleTo_middle_eq (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ) :
    contentETripleTo D Sc cutoff N β i j l γ h =
      contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ) ⋙
        contentInductionTo D Sc cutoff N δ [l] γ hγ := by
  subst δ
  rfl

/-- Intermediate-content recast, with no crossing in its definition. -/
def contentETripleMiddleIso (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ) :
    contentETripleTo D Sc cutoff N β i j l γ h ≅
      contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ) ⋙
        contentInductionTo D Sc cutoff N δ [l] γ hγ :=
  eqToIso (contentETripleTo_middle_eq D Sc cutoff N β i j l δ γ hδ h hγ)

/-- The pair-first comparison permits any explicitly identified intermediate content. -/
theorem contentETripleComparison_middle (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ) :
    contentETripleComparison D Sc cutoff N β i j l γ h =
      contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ ≪≫
      Functor.isoWhiskerRight
        (contentEPairToComparison D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ))
        (contentInductionTo D Sc cutoff N δ [l] γ hγ) ≪≫
      contentInductionCompTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ)
        [l] γ hγ h := by
  subst δ
  simp only [contentETripleMiddleIso, eqToIso_refl, Iso.refl_trans]
  rfl

private def compIsoApp {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E) (e : J ⋙ K ≅ L) (M : C) :
    K.obj (J.obj M) ≅ L.obj M := e.app M

private def isoCompApp {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (V : C ⥤ E) (J : C ⥤ B) (K : B ⥤ E) (e : V ≅ J ⋙ K) (M : C) :
    V.obj M ≅ K.obj (J.obj M) := e.app M

private theorem compIsoApp_hom_mem
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E) (e : J ⋙ K ≅ L) (M : C)
    {p : ZMod 2} (he : e.hom.app M ∈ parity (R := k) _ _ p) :
    (compIsoApp J K L e M).hom ∈ parity (R := k) _ _ p := he

private theorem prefixComparison_app_canonical
    {C B : Type*} {T : Type u} [Category* C] [Category* B]
    [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]
    (G H : C ⥤ B) (K : B ⥤ Superfunctor k T (SVec k))
    (F R : C ⥤ Superfunctor k T (SVec k))
    (e₀ : F ≅ G ⋙ K) (e₁ : G ≅ H) (e₂ : H ⋙ K ≅ R) (M : C) :
    ((e₀ ≪≫ Functor.isoWhiskerRight e₁ K ≪≫ e₂).app M) =
      isoCompApp F G K e₀ M ≪≫ K.mapIso (e₁.app M) ≪≫ compIsoApp H K R e₂ M := by
  apply Iso.ext
  simp only [isoCompApp, compIsoApp, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.mapIso_hom]

private theorem prefixComparison_app
    {C B : Type*} {T : Type u} [Category* C] [Category* B]
    [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]
    (G H : C ⥤ B) (K : B ⥤ Superfunctor k T (SVec k))
    (F R : C ⥤ Superfunctor k T (SVec k))
    (e₀ : F ≅ G ⋙ K) (e₁ : G ≅ H) (e₂ : H ⋙ K ≅ R) (M : C) :
    ((e₀ ≪≫ Functor.isoWhiskerRight e₁ K ≪≫ e₂).app M) =
      e₀.app M ≪≫ K.mapIso (e₁.app M) ≪≫ e₂.app M := by
  apply Iso.ext
  simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.mapIso_hom]

private theorem prefixIso_linearEquiv
    {C B : Type*} {T : Type u} [Category* C] [Category* B]
    [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]
    (G H : C ⥤ B) (K : B ⥤ Superfunctor k T (SVec k))
    (F R : C ⥤ Superfunctor k T (SVec k))
    (e₀ : F ≅ G ⋙ K) (e₁ : G ≅ H) (e₂ : H ⋙ K ≅ R) (M : C) (z : T) :
    moduleIsoLinearEquiv ((e₀ ≪≫ Functor.isoWhiskerRight e₁ K ≪≫ e₂).app M) z =
      (moduleIsoLinearEquiv (e₀.app M) z).trans
        ((moduleIsoLinearEquiv (K.mapIso (e₁.app M)) z).trans
          (moduleIsoLinearEquiv (e₂.app M) z)) := by
  rw [prefixComparison_app, moduleIsoLinearEquiv_trans, moduleIsoLinearEquiv_trans]

theorem contentETripleEquiv_prefix (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleEquiv D Sc cutoff N β i j l γ h M z =
      (moduleIsoLinearEquiv ((contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ).app M) z).trans
        ((moduleIsoLinearEquiv
          ((contentInductionTo D Sc cutoff N δ [l] γ hγ).mapIso
            ((contentEPairToComparison D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).app M)) z).trans
          (moduleIsoLinearEquiv
            ((contentInductionCompTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ)
              [l] γ hγ h).app M) z)) := by
  unfold contentETripleEquiv
  rw [contentETripleComparison_middle D Sc cutoff N β i j l δ γ hδ h hγ]
  exact prefixIso_linearEquiv _ _ _ _ _ _ _ _ M z

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

private def comparisonConjugate {C : Type*} [Category* C]
    {V V' W W' : C} (g : V ≅ W) (g' : V' ≅ W') (c : W' ⟶ W) : V' ⟶ V :=
  (g'.hom ≫ c) ≫ g.inv

private theorem comparisonConjugate_app
    {C E : Type*} [Category* C] [Category* E]
    {F G F' G' : C ⥤ E} (g : F ≅ G) (g' : F' ≅ G') (M : C)
    (a : G'.obj M ⟶ G.obj M) :
    ((g'.hom.app M ≫ a) ≫ g.inv.app M) =
      comparisonConjugate (g.app M) (g'.app M) a := by
  unfold comparisonConjugate
  simp only [Iso.app_hom, Iso.app_inv]

private theorem prefixModuleSquare
    {B C : Type*} [Category* B] [Category* C]
    (K : B ⥤ C) {A B₁ A' B₁' : B}
    (e : A ≅ B₁) (e' : A' ≅ B₁') (a : B₁' ⟶ B₁)
    {V V' W W' : C} (d : V ≅ K.obj A) (d' : V' ≅ K.obj A')
    (f : K.obj B₁ ≅ W) (f' : K.obj B₁' ≅ W') (c : W' ⟶ W)
    (h : K.map a ≫ f.hom = f'.hom ≫ c) :
    (((d' ≪≫ K.mapIso e' ≪≫ f').hom ≫ c) ≫ (d ≪≫ K.mapIso e ≪≫ f).inv) =
      ((d'.hom ≫ K.map ((e'.hom ≫ a) ≫ e.inv)) ≫ d.inv) := by
  have hx := congrArg
    (fun t : K.obj B₁' ⟶ W =>
      d'.hom ≫ K.map e'.hom ≫ t ≫ f.inv ≫ K.map e.inv ≫ d.inv) h
  simpa only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] using hx.symm

private theorem prefixModuleSquare_eq
    {B C : Type*} [Category* B] [Category* C]
    (K : B ⥤ C) {A B₁ A' B₁' : B}
    (e : A ≅ B₁) (e' : A' ≅ B₁') (a : B₁' ⟶ B₁)
    {V V' W W' : C} (d : V ≅ K.obj A) (d' : V' ≅ K.obj A')
    (f : K.obj B₁ ≅ W) (f' : K.obj B₁' ≅ W') (c : W' ⟶ W)
    (g : V ≅ W) (g' : V' ≅ W') (b : A' ⟶ A)
    (hg : g = d ≪≫ K.mapIso e ≪≫ f) (hg' : g' = d' ≪≫ K.mapIso e' ≪≫ f')
    (hb : b = (e'.hom ≫ a) ≫ e.inv)
    (h : K.map a ≫ f.hom = f'.hom ≫ c) :
    comparisonConjugate g g' c = comparisonConjugate d d' (K.map b) := by
  unfold comparisonConjugate
  rw [hg, hg', hb]
  exact prefixModuleSquare K e e' a d d' f f' c h

/-- The prefix pair crossing is an independently induced module morphism. -/
def contentPrefixCrossMorphism (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    (contentETripleTo D Sc cutoff N β j i l γ ht).obj M ⟶
      (contentETripleTo D Sc cutoff N β i j l γ h).obj M :=
  comparisonConjugate (C := ContentModules D Sc cutoff N γ)
    (V := (contentETripleTo D Sc cutoff N β i j l γ h).obj M)
    (V' := (contentETripleTo D Sc cutoff N β j i l γ ht).obj M)
    (W := (contentInductionTo D Sc cutoff N δ [l] γ hγ).obj
      ((contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).obj M))
    (W' := (contentInductionTo D Sc cutoff N δ [l] γ hγ).obj
      ((contentEPairTo D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ')).obj M))
    (isoCompApp
    (contentETripleTo D Sc cutoff N β i j l γ h)
    (contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ))
    (contentInductionTo D Sc cutoff N δ [l] γ hγ)
    (contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ) M)
    (isoCompApp
    (contentETripleTo D Sc cutoff N β j i l γ ht)
    (contentEPairTo D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ'))
    (contentInductionTo D Sc cutoff N δ [l] γ hγ)
    (contentETripleMiddleIso D Sc cutoff N β j i l δ γ hδ' ht hγ) M)
    ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
      (X := (contentEPairTo D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ')).obj M)
      (Y := (contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).obj M)
      ((contentEPairCrossTransform D Sc cutoff N β i j δ
        ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
        (D.parity i * D.parity j) M))

def contentPrefixCrossComponent (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :=
  (contentPrefixCrossMorphism D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M).total z

section PrefixComparisonPremises
variable
  (β : Multiset I) (i j l : I) (δ γ : Multiset I)
  (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
  (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([j,i,l] : Multiset I) = γ)
  (hγ : δ + ([l] : Multiset I) = γ)
  (M : ContentModules D Sc cutoff N β)


private theorem prefixTransform_component :
    (contentETripleTransform D Sc cutoff N (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := j) (b := i) (c := l) h ht
      (contentTriplePrefixAffine_mem D Sc i j l)).app (D.parity i * D.parity j) M =
      comparisonConjugate (C := ContentModules D Sc cutoff N γ)
        (V := (contentETripleTo D Sc cutoff N β i j l γ h).obj M)
        (V' := (contentETripleTo D Sc cutoff N β j i l γ ht).obj M)
        (W := (contentInductionTo D Sc cutoff N β [i,j,l] γ h).obj M)
        (W' := (contentInductionTo D Sc cutoff N β [j,i,l] γ ht).obj M)
        ((contentETripleComparison D Sc cutoff N β i j l γ h).app M)
        ((contentETripleComparison D Sc cutoff N β j i l γ ht).app M)
        ((contentInductionTransform D Sc cutoff N (β := β) (γ := γ)
      (σ := [i,j,l]) (τ := [j,i,l]) h ht (contentTriplePrefixAffine_mem D Sc i j l)).app
      (D.parity i * D.parity j) M) := by
  exact (contentETripleTransform_component D Sc cutoff N (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := j) (b := i) (c := l) h ht
    (contentTriplePrefixAffine_mem D Sc i j l) M).trans
    (comparisonConjugate_app
      (F := contentETripleTo D Sc cutoff N β i j l γ h)
      (G := contentInductionTo D Sc cutoff N β [i,j,l] γ h)
      (F' := contentETripleTo D Sc cutoff N β j i l γ ht)
      (G' := contentInductionTo D Sc cutoff N β [j,i,l] γ ht)
      (contentETripleComparison D Sc cutoff N β i j l γ h)
      (contentETripleComparison D Sc cutoff N β j i l γ ht) M
      ((contentInductionTransform D Sc cutoff N (β := β) (γ := γ)
      (σ := [i,j,l]) (τ := [j,i,l]) h ht (contentTriplePrefixAffine_mem D Sc i j l)).app
      (D.parity i * D.parity j) M))

private theorem prefixComparison_at :
    (contentETripleComparison D Sc cutoff N β i j l γ h).app M =
      (isoCompApp
    (contentETripleTo D Sc cutoff N β i j l γ h)
    (contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ))
    (contentInductionTo D Sc cutoff N δ [l] γ hγ)
    (contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ) M) ≪≫
        (contentInductionTo D Sc cutoff N δ [l] γ hγ).mapIso ((contentEPairToComparison D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).app M) ≪≫
        (compIsoApp
    (contentInductionTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ))
    (contentInductionTo D Sc cutoff N δ [l] γ hγ)
    (contentInductionTo D Sc cutoff N β [i,j,l] γ h)
    (contentInductionCompTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ)
      [l] γ hγ h) M) := by
  rw [contentETripleComparison_middle D Sc cutoff N β i j l δ γ hδ h hγ]
  exact prefixComparison_app_canonical _ _ _ _ _ _ _ _ M


private theorem prefixPair_component : ((contentEPairCrossTransform D Sc cutoff N β i j δ
    ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
    (D.parity i * D.parity j) M) = (((contentEPairToComparison D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ')).app M).hom ≫ ((contentInductionTransform D Sc cutoff N (β := β) (γ := δ)
    (σ := [i,j]) (τ := [j,i]) ((contentPair_sum β i j).trans hδ)
    ((contentPair_sum β j i).trans hδ') (contentCrossAffine_mem D Sc i j)).app
    (D.parity i * D.parity j) M)) ≫ ((contentEPairToComparison D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).app M).inv :=
  contentEPairCross_component D Sc cutoff N β i j δ
    ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ') M


private theorem prefixInner_map :
    (contentInductionTo D Sc cutoff N δ [l] γ hγ).map ((contentInductionTransform D Sc cutoff N (β := β) (γ := δ)
    (σ := [i,j]) (τ := [j,i]) ((contentPair_sum β i j).trans hδ)
    ((contentPair_sum β j i).trans hδ') (contentCrossAffine_mem D Sc i j)).app
    (D.parity i * D.parity j) M) ≫
      (compIsoApp
    (contentInductionTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ))
    (contentInductionTo D Sc cutoff N δ [l] γ hγ)
    (contentInductionTo D Sc cutoff N β [i,j,l] γ h)
    (contentInductionCompTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ)
      [l] γ hγ h) M).hom =
      (compIsoApp
    (contentInductionTo D Sc cutoff N β [j,i] δ ((contentPair_sum β j i).trans hδ'))
    (contentInductionTo D Sc cutoff N δ [l] γ hγ)
    (contentInductionTo D Sc cutoff N β [j,i,l] γ ht)
    (contentInductionCompTo D Sc cutoff N β [j,i] δ ((contentPair_sum β j i).trans hδ')
      [l] γ hγ ht) M).hom ≫ ((contentInductionTransform D Sc cutoff N (β := β) (γ := γ)
    (σ := [i,j,l]) (τ := [j,i,l]) h ht (contentTriplePrefixAffine_mem D Sc i j l)).app
    (D.parity i * D.parity j) M) :=
  contentInductionCompTo_inner_map_of_eq D Sc cutoff N β [i,j] [j,i] δ
    ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ') [l] γ hγ h ht
    (contentCrossAffine_mem D Sc i j) (contentTriplePrefixAffine_mem D Sc i j l)
    (contentTriplePrefixAffine_eq_whisker D Sc i j l) M


end PrefixComparisonPremises

theorem contentETripleTransform_prefix_cross (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (ht : β + ([j,i,l] : Multiset I) = γ) (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    (contentETripleTransform D Sc cutoff N (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := j) (b := i) (c := l) h ht
      (contentTriplePrefixAffine_mem D Sc i j l)).app (D.parity i * D.parity j) M =
      contentPrefixCrossMorphism D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M := by
    exact (prefixTransform_component D Sc cutoff N β i j l γ h ht M).trans
      (prefixModuleSquare_eq
      (B := ContentModules D Sc cutoff N δ) (C := ContentModules D Sc cutoff N γ)
      (A := (contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).obj M)
      (B₁ := (contentInductionTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ)).obj M)
      (A' := (contentEPairTo D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ')).obj M)
      (B₁' := (contentInductionTo D Sc cutoff N β [j,i] δ ((contentPair_sum β j i).trans hδ')).obj M)
      (V := (contentETripleTo D Sc cutoff N β i j l γ h).obj M)
      (V' := (contentETripleTo D Sc cutoff N β j i l γ ht).obj M)
      (W := (contentInductionTo D Sc cutoff N β [i,j,l] γ h).obj M)
      (W' := (contentInductionTo D Sc cutoff N β [j,i,l] γ ht).obj M)
      (contentInductionTo D Sc cutoff N δ [l] γ hγ)
      ((contentEPairToComparison D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ)).app M)
      ((contentEPairToComparison D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ')).app M)
      ((contentInductionTransform D Sc cutoff N (β := β) (γ := δ)
        (σ := [i,j]) (τ := [j,i]) ((contentPair_sum β i j).trans hδ)
        ((contentPair_sum β j i).trans hδ') (contentCrossAffine_mem D Sc i j)).app
        (D.parity i * D.parity j) M)
      (isoCompApp
      (contentETripleTo D Sc cutoff N β i j l γ h)
      (contentEPairTo D Sc cutoff N β i j δ ((contentPair_sum β i j).trans hδ))
      (contentInductionTo D Sc cutoff N δ [l] γ hγ)
      (contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ) M)
      (isoCompApp
      (contentETripleTo D Sc cutoff N β j i l γ ht)
      (contentEPairTo D Sc cutoff N β j i δ ((contentPair_sum β j i).trans hδ'))
      (contentInductionTo D Sc cutoff N δ [l] γ hγ)
      (contentETripleMiddleIso D Sc cutoff N β j i l δ γ hδ' ht hγ) M)
      (compIsoApp
      (contentInductionTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ))
      (contentInductionTo D Sc cutoff N δ [l] γ hγ)
      (contentInductionTo D Sc cutoff N β [i,j,l] γ h)
      (contentInductionCompTo D Sc cutoff N β [i,j] δ ((contentPair_sum β i j).trans hδ)
        [l] γ hγ h) M)
      (compIsoApp
      (contentInductionTo D Sc cutoff N β [j,i] δ ((contentPair_sum β j i).trans hδ'))
      (contentInductionTo D Sc cutoff N δ [l] γ hγ)
      (contentInductionTo D Sc cutoff N β [j,i,l] γ ht)
      (contentInductionCompTo D Sc cutoff N β [j,i] δ ((contentPair_sum β j i).trans hδ')
        [l] γ hγ ht) M)
      ((contentInductionTransform D Sc cutoff N (β := β) (γ := γ)
        (σ := [i,j,l]) (τ := [j,i,l]) h ht
        (contentTriplePrefixAffine_mem D Sc i j l)).app (D.parity i * D.parity j) M)
      ((contentETripleComparison D Sc cutoff N β i j l γ h).app M)
      ((contentETripleComparison D Sc cutoff N β j i l γ ht).app M)
      ((contentEPairCrossTransform D Sc cutoff N β i j δ
        ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
        (D.parity i * D.parity j) M)
      (prefixComparison_at D Sc cutoff N β i j l δ γ hδ h hγ M)
      (prefixComparison_at D Sc cutoff N β j i l δ γ hδ' ht hγ M)
      (prefixPair_component D Sc cutoff N β i j δ hδ hδ' M)
      (prefixInner_map D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M))

/-- Evaluation of the independently induced prefix crossing. -/
theorem contentETripleMap_prefix_cross (β : Multiset I) (i j l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (ht : β + ([j,i,l] : Multiset I) = γ) (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := j) (b := i) (c := l) h ht
      (contentTriplePrefixAffine_mem D Sc i j l) M z =
      contentPrefixCrossComponent D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M z := by
  have hx := congrArg (fun f => f.total z)
    (contentETripleTransform_prefix_cross D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M)
  rw [contentETripleTransform_total D Sc cutoff N (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := j) (b := i) (c := l) h ht
    (contentTriplePrefixAffine_mem D Sc i j l) M z] at hx
  exact hx
end OddMath.QuiverHecke.ELVOld

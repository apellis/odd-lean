/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionAssociativity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # Content induction and independent whiskering

The canonical content composition comparison intertwines the independently
defined inner and outer module transformations of an affine endomorphism.
Both content equality transports are retained. The source comparisons are
proved through tensor coefficients and the truncated quotient, not assumed.
These squares identify the transported positioned dots with whiskered
single-letter dots in the content E-action assembly.
-/

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
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : C ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

theorem compForward_inner_recast (e : J ⋙ K = L) {p : ZMod 2}
    {a : ∀ v, J.obj v ⟶ J.obj v} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (K.map (a v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    let c := inductionComp J K ≪≫ eqToIso
      (show induction (k := k) (J ⋙ K) = induction L by subst L; rfl)
    (moduleIsoLinearEquiv (c.app M) z).toLinearMap ∘ₗ
        mapComponent K (transformComponent ha M) p z =
      transformLinear hb M z ∘ₗ (moduleIsoLinearEquiv (c.app M) z).toLinearMap := by
  subst L
  have hab' : (fun v => K.map (a v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_inner K ha M z

theorem compForward_outer_recast (e : J ⋙ K = L) {p : ZMod 2}
    {a : ∀ w, K.obj w ⟶ K.obj w} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (a (J.obj v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    let c := inductionComp J K ≪≫ eqToIso
      (show induction (k := k) (J ⋙ K) = induction L by subst L; rfl)
    (moduleIsoLinearEquiv (c.app M) z).toLinearMap ∘ₗ
        transformLinear ha (induced J M) z =
      transformLinear hb M z ∘ₗ (moduleIsoLinearEquiv (c.app M) z).toLinearMap := by
  subst L
  have hab' : (fun v => a (J.obj v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_outer J ha M z

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld
open MonoidalCategory
open scoped TensorProduct
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem whiskerRecast_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

theorem appendComponent_rightContext_heq (v σ τ : List I)
    (a : End ((pres D Sc).obj (ob D σ))) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (v ++ σ)
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
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact whiskerRecast_map_heq
    (A := fun w : List I => End ((pres D Sc).obj (ob D w)))
    (B := fun w : List I => TruncatedOld D Sc cutoff N w w)
    (fun w f => (truncatedIdeal D Sc cutoff N w w).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (List.append_assoc v σ τ) hh

theorem appendComponent_leftContext_heq (v σ τ : List I)
    (a : End ((pres D Sc).obj (ob D τ))) :
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
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact whiskerRecast_map_heq
    (A := fun w : List I => End ((pres D Sc).obj (ob D w)))
    (B := fun w : List I => TruncatedOld D Sc cutoff N w w)
    (fun w f => (truncatedIdeal D Sc cutoff N w w).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (List.append_assoc v σ τ) hh

/-- Inner module whiskering equals right whiskering of the affine source. -/
theorem contentInductionComp_inner (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.mapComponent (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha) M) p z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_inner_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha)
    (contentAppendTo_supernatural D Sc cutoff N h' h'
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha))
    (fun v => appendComponent_rightContext_heq D Sc cutoff N v.obj.word σ τ a) M z

/-- Outer module whiskering equals left whiskering of the affine source. -/
theorem contentInductionComp_outer (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D τ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h h ha)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ _ rfl) M) z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_outer_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppendTo_supernatural D Sc cutoff N h h ha)
    (contentAppendTo_supernatural D Sc cutoff N h' h'
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha))
    (fun v => appendComponent_leftContext_heq D Sc cutoff N v.obj.word σ τ a) M z

end OddMath.QuiverHecke.ELVOld

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering

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

end OddMath.QuiverHecke.ELVOld

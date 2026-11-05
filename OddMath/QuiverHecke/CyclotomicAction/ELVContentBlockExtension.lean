/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedExtension
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform

/-! # Extension from a full truncated content block

The canonical multiset content module realization of Brundan–Ellis
(1.12) uses extension along the literal full content inclusion. Its unit
is invertible and its counit is invertible on supported modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

instance contentInclusion_additive (β : Multiset I) :
    (contentInclusion D Sc cutoff N β).Additive where
  map_add := by intros; rfl
instance contentInclusion_linear (β : Multiset I) :
    (contentInclusion D Sc cutoff N β).Linear k where
  map_smul := by intros; rfl
instance contentInclusion_super (β : Multiset I) :
    IsSuperfunctor k (contentInclusion D Sc cutoff N β) where
  map_mem h := h

/-- Content conservation descends through the literal truncated quotient. -/
theorem truncatedCategory_hom_eq_zero_of_content_ne
    {v w : TruncatedCategory D Sc cutoff N}
    (h : (v.word : Multiset I) ≠ (w.word : Multiset I)) (f : v ⟶ w) : f = 0 := by
  obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
  have hp : ¬ w.word.Perm v.word := fun hp => h (Multiset.coe_eq_coe.mpr hp.symm)
  rw [hom_eq_zero_of_not_perm D Sc cutoff hp a, map_zero]

/-- The chosen full-inclusion unit recovers every exact-content module. -/
def contentExtensionUnitIso (β : Multiset I) (M : ContentModules D Sc cutoff N β) :
    M ≅ (BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj
      (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M) :=
  BalancedInduction.fullyFaithfulUnitIso (contentInclusion D Sc cutoff N β) M

/-- Support means literal zero components outside the chosen colour multiset. -/
def ContentSupported (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) : Prop :=
  ∀ w : TruncatedCategory D Sc cutoff N, (w.word : Multiset I) ≠ β →
    Subsingleton (M.obj w)

theorem contentExtension_supported (β : Multiset I)
    (M : Superfunctor k (ContentCategory D Sc cutoff N β) (SVec k)) :
    ContentSupported D Sc cutoff N β
      (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M) := by
  intro w hw
  have hz : ∀ z : BalancedInduction.Obj (contentInclusion D Sc cutoff N β) M.toFunctor w,
      z = 0 := by
    apply BalancedInduction.obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply truncatedCategory_hom_eq_zero_of_content_ne D Sc cutoff N (f := g)
    intro he
    exact hw (he.symm.trans s.content)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem contentSupportedCounit_bijective (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) (w : TruncatedCategory D Sc cutoff N) :
    Function.Bijective (BalancedInduction.counit (contentInclusion D Sc cutoff N β)
      M.toFunctor w) := by
  classical
  by_cases hw : (w.word : Multiset I) = β
  · exact BalancedInduction.counit_bijective_at_image
      (contentInclusion D Sc cutoff N β) M.toFunctor
      ⟨w, hw⟩
  · have hsource := contentExtension_supported D Sc cutoff N β
      ((BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj M) w hw
    have htarget := hM w hw
    exact ⟨fun x y _ => hsource.elim x y, fun y => ⟨0, htarget.elim _ y⟩⟩

/-- The forward map is precisely the established balanced inclusion counit. -/
def contentSupportedCounitEquiv (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) (w : TruncatedCategory D Sc cutoff N) :
    BalancedInduction.Obj (contentInclusion D Sc cutoff N β)
        (contentInclusion D Sc cutoff N β ⋙ M.toFunctor) w ≃ₗ[k] M.obj w :=
  LinearEquiv.ofBijective _ (contentSupportedCounit_bijective D Sc cutoff N β M hM w)

def contentSupportedCounitNatIso (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) :
    (BalancedInduction.induced (contentInclusion D Sc cutoff N β)
      ((BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj M)).toFunctor ≅
        M.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit (contentInclusion D Sc cutoff N β) M.toFunctor w
      inv := (contentSupportedCounitEquiv D Sc cutoff N β M hM w).symm.toLinearMap
      hom_inv_id := by
        ext z
        exact (contentSupportedCounitEquiv D Sc cutoff N β M hM w).symm_apply_apply z
      inv_hom_id := by
        ext z
        exact (contentSupportedCounitEquiv D Sc cutoff N β M hM w).apply_symm_apply z })
    (fun a => BalancedInduction.counit_naturality (contentInclusion D Sc cutoff N β)
      M.toFunctor a)

/-- Supported modules are recovered by the actual even inclusion counit. -/
def contentSupportedCounitIso (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) :
    BalancedInduction.induced (contentInclusion D Sc cutoff N β)
      ((BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj M) ≅ M :=
  moduleIsoOfEvenNatIso _ _ (contentSupportedCounitNatIso D Sc cutoff N β M hM)
    (fun w => BalancedInduction.counit_mem (contentInclusion D Sc cutoff N β) M w)
    (fun w => Supercategory.inv_mem
      ((contentSupportedCounitNatIso D Sc cutoff N β M hM).app w)
      (BalancedInduction.counit_mem (contentInclusion D Sc cutoff N β) M w))

theorem contentSupportedCounitIso_hom (β : Multiset I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N β M) :
    (contentSupportedCounitIso D Sc cutoff N β M hM).hom =
      (BalancedInduction.adjunctionCounit (contentInclusion D Sc cutoff N β)).app M := by
  apply Superfunctor.hom_ext
  intro p w
  rfl

end OddMath.QuiverHecke.ELVOld

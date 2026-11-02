import OddMath.QuiverHecke.CyclotomicAction.ELVFullyFaithfulInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVOffContentZero

/-! # Canonical extension and support on an old content block

Content conservation makes extension by the full content inclusion zero off
that content. On supported modules the actual inclusion counit is invertible.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Preadditive E] [Linear k E]
  (J : C ⥤ E)

omit [Preadditive C] [Linear k C] in
theorem obj_eq_zero_of_coeff_eq_zero (M : C ⥤ SVec k) (w : E)
    (h : ∀ s (g : J.obj s ⟶ w), g = 0) (z : Obj J M w) : z = 0 := by
  have hz : (LinearMap.id : Obj J M w →ₗ[k] Obj J M w) = 0 := by
    apply hom_ext
    intro s g b
    change tensor J M s g b = 0
    rw [h s g]
    exact tensor_zero_left J M s b
  exact LinearMap.congr_fun hz z

variable [J.Full] [J.Faithful] [J.Additive] [J.Linear k]
  (N : E ⥤ SVec k) [N.Additive] [N.Linear k]

theorem counit_eq_fullyFaithfulUnitInverse (v : C) :
    counit J N (J.obj v) = fullyFaithfulUnitInverse J (J ⋙ N) v := by
  apply hom_ext
  intro s g b
  rw [counit_tensor]
  have he := fullyFaithfulUnitInverse_tensor J (J ⋙ N) v s g b
  change fullyFaithfulUnitInverse J (J ⋙ N) v (tensor J (J ⋙ N) s g b) =
    N.map (J.map (J.preimage g)) b at he
  rw [Functor.map_preimage] at he
  exact he.symm

theorem counit_bijective_at_image (v : C) :
    Function.Bijective (counit J N (J.obj v)) := by
  rw [counit_eq_fullyFaithfulUnitInverse]
  have hleft := fullyFaithfulUnitInverse_unit J (J ⋙ N) v
  have hright := unit_fullyFaithfulUnitInverse J (J ⋙ N) v
  exact ⟨fun x y h => by
    have hx := LinearMap.congr_fun hright x
    have hy := LinearMap.congr_fun hright y
    change unit J (J ⋙ N) v (fullyFaithfulUnitInverse J (J ⋙ N) v x) = x at hx
    change unit J (J ⋙ N) v (fullyFaithfulUnitInverse J (J ⋙ N) v y) = y at hy
    exact hx.symm.trans ((congrArg (unit J (J ⋙ N) v) h).trans hy),
    fun y => ⟨unit J (J ⋙ N) v y, LinearMap.congr_fun hleft y⟩⟩

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Support means literal zero components outside the chosen colour multiset. -/
def OldContentSupported (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) : Prop :=
  ∀ w : OldCategory D Sc cutoff, (w.word : Multiset I) ≠ (ν : Multiset I) →
    Subsingleton (N.obj w)

theorem oldContentExtension_supported (ν : List I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    OldContentSupported D Sc cutoff ν
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) := by
  intro w hw
  have hz : ∀ z : BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν) M.toFunctor w,
      z = 0 := by
    apply BalancedInduction.obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply oldCategory_hom_eq_zero_of_content_ne D Sc cutoff (f := g)
    intro he
    exact hw (he.symm.trans (Multiset.coe_eq_coe.mpr s.wordPerm))
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem supported_contentCounit_bijective (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) (w : OldCategory D Sc cutoff) :
    Function.Bijective (BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
      N.toFunctor w) := by
  classical
  by_cases hw : (w.word : Multiset I) = (ν : Multiset I)
  · exact BalancedInduction.counit_bijective_at_image
      (oldContentInclusion D Sc cutoff ν) N.toFunctor
      ⟨w, Multiset.coe_eq_coe.mp hw⟩
  · have hsource := oldContentExtension_supported D Sc cutoff ν
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N) w hw
    have htarget := hN w hw
    exact ⟨fun x y _ => hsource.elim x y, fun y => ⟨0, htarget.elim _ y⟩⟩

/-- The forward map is precisely the established balanced inclusion counit. -/
def supportedContentCounitEquiv (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        (oldContentInclusion D Sc cutoff ν ⋙ N.toFunctor) w ≃ₗ[k] N.obj w :=
  LinearEquiv.ofBijective _ (supported_contentCounit_bijective D Sc cutoff ν N hN w)

def supportedContentCounitNatIso (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N)).toFunctor ≅
        N.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit (oldContentInclusion D Sc cutoff ν) N.toFunctor w
      inv := (supportedContentCounitEquiv D Sc cutoff ν N hN w).symm.toLinearMap
      hom_inv_id := by
        ext z
        exact (supportedContentCounitEquiv D Sc cutoff ν N hN w).symm_apply_apply z
      inv_hom_id := by
        ext z
        exact (supportedContentCounitEquiv D Sc cutoff ν N hN w).apply_symm_apply z })
    (fun a => BalancedInduction.counit_naturality (oldContentInclusion D Sc cutoff ν)
      N.toFunctor a)

/-- Supported modules are recovered by the actual even inclusion counit. -/
def supportedContentCounitIso (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N) ≅ N :=
  moduleIsoOfEvenNatIso _ _ (supportedContentCounitNatIso D Sc cutoff ν N hN)
    (fun w => BalancedInduction.counit_mem (oldContentInclusion D Sc cutoff ν) N w)
    (fun w => Supercategory.inv_mem
      ((supportedContentCounitNatIso D Sc cutoff ν N hN).app w)
      (BalancedInduction.counit_mem (oldContentInclusion D Sc cutoff ν) N w))

theorem supportedContentCounitIso_hom (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    (supportedContentCounitIso D Sc cutoff ν N hN).hom =
      (BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app N := by
  apply Superfunctor.hom_ext
  intro p w
  rfl

end OddMath.QuiverHecke.ELVOld

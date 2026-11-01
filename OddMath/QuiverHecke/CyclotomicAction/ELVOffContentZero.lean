import OddMath.QuiverHecke.CyclotomicAction.ELVKernelDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading

/-! # Off-content coefficient-kernel components vanish

A pure IndRes coefficient tensor has arrows v → J(s) → t. When v and t
have different colour content, at least one arrow is zero. Thus the actual
balanced quotient is zero, without finite colours, degree bounds, or a
whole-category/content equivalence. This supplies the zero branch for a
fixed-target finite matrix count on the full old coefficient category.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Content conservation descends through the actual old cyclotomic quotient. -/
theorem old_eq_zero_of_not_perm {v t : List I} (h : ¬ t.Perm v)
    (f : Old D Sc cutoff v t) : f = 0 := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective f
  rw [hom_eq_zero_of_not_perm D Sc cutoff h r, map_zero]

theorem old_eq_zero_of_content_ne {v t : List I}
    (h : (v : Multiset I) ≠ (t : Multiset I)) (f : Old D Sc cutoff v t) : f = 0 := by
  apply old_eq_zero_of_not_perm D Sc cutoff (f := f)
  intro hp
  exact h (Multiset.coe_eq_coe.mpr hp.symm)

theorem oldCategory_hom_eq_zero_of_content_ne {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) (f : v ⟶ t) : f = 0 :=
  old_eq_zero_of_content_ne D Sc cutoff h f

theorem append_content_ne (i : I) {v t : List I}
    (h : (v : Multiset I) ≠ (t : Multiset I)) :
    ((v ++ [i] : List I) : Multiset I) ≠ ((t ++ [i] : List I) : Multiset I) := by
  intro he
  apply h
  change (v : Multiset I) + ([i] : Multiset I) = (t : Multiset I) + ([i] : Multiset I) at he
  exact add_right_cancel he

theorem append_hom_eq_zero_of_content_ne (i : I) {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I))
    (f : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) : f = 0 :=
  old_eq_zero_of_content_ne D Sc cutoff (append_content_ne i h) f

theorem oldCategory_hom_subsingleton_of_content_ne {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) : Subsingleton (v ⟶ t) :=
  ⟨fun f g => (oldCategory_hom_eq_zero_of_content_ne D Sc cutoff h f).trans
    (oldCategory_hom_eq_zero_of_content_ne D Sc cutoff h g).symm⟩

theorem append_hom_subsingleton_of_content_ne (i : I) {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Subsingleton ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :=
  ⟨fun f g => (append_hom_eq_zero_of_content_ne D Sc cutoff i h f).trans
    (append_hom_eq_zero_of_content_ne D Sc cutoff i h g).symm⟩

/-- Every component of this double coend vanishes off content, for any source functor J. -/
theorem indResKernel_eq_zero_of_content_ne
    {C : Type u} [Category.{u} C] (J : C ⥤ OldCategory D Sc cutoff)
    {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I))
    (z : IndResKernel.Component (k := k) J v t) : z = 0 := by
  classical
  have hz : (LinearMap.id : IndResKernel.Component (k := k) J v t →ₗ[k]
      IndResKernel.Component (k := k) J v t) = 0 := by
    apply BalancedInduction.hom_ext
    intro s g b
    change BalancedInduction.tensor J (J ⋙ IndResKernel.homModule (k := k) v) s g b = 0
    by_cases hs : (v.word : Multiset I) = ((J.obj s).word : Multiset I)
    · have hg : g = 0 := oldCategory_hom_eq_zero_of_content_ne D Sc cutoff
        (fun he => h (hs.trans he)) g
      rw [hg]
      exact BalancedInduction.tensor_zero_left J (J ⋙ IndResKernel.homModule (k := k) v) s b
    · have hb : b = 0 := oldCategory_hom_eq_zero_of_content_ne D Sc cutoff hs b
      rw [hb]
      exact BalancedInduction.tensor_zero_right J (J ⋙ IndResKernel.homModule (k := k) v) s g
  exact LinearMap.congr_fun hz z

theorem indResKernel_subsingleton_of_content_ne
    {C : Type u} [Category.{u} C] (J : C ⥤ OldCategory D Sc cutoff)
    {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Subsingleton (IndResKernel.Component (k := k) J v t) :=
  ⟨fun x y => (indResKernel_eq_zero_of_content_ne D Sc cutoff J h x).trans
    (indResKernel_eq_zero_of_content_ne D Sc cutoff J h y).symm⟩

end OddMath.QuiverHecke.ELVOld

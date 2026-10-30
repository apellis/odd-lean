/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients
/-! # Faithfulness of the exact-content coefficient realization

Covariant source representables are actual objects of `ContentModules`.
Evaluation at their identity detects every central coefficient component.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)

def contentHomSpace (v w : ContentCategory D Sc cutoff N β) : SVec k where
  carrier := v ⟶ w
  odd := proj k 1
  odd_comp_odd := by ext f; exact proj_proj 1 f

theorem contentHomSpace_part (v w : ContentCategory D Sc cutoff N β) (p : ZMod 2) :
    (contentHomSpace D Sc cutoff N β v w).part p = parity (R := k) v w p := by
  ext (f : v ⟶ w)
  refine (SVec.mem_part_iff (contentHomSpace D Sc cutoff N β v w)).trans ?_
  have hp : (contentHomSpace D Sc cutoff N β v w).proj p f = proj k p f := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · change f - proj k 1 f = proj k 0 f
      exact eq_sub_iff_add_eq.mpr (proj_add_proj f) |>.symm
    · rfl
  rw [hp]
  exact ⟨fun h => h ▸ proj_mem p f, proj_of_mem⟩

def contentRepresentableFunctor (v : ContentCategory D Sc cutoff N β) :
    ContentCategory D Sc cutoff N β ⥤ SVec k where
      obj := contentHomSpace D Sc cutoff N β v
      map := fun f => { toFun := fun h => h ≫ f
                        map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _
                        map_smul' := fun r h => Linear.smul_comp _ _ _ _ _ _ }
      map_id := fun w => by ext h; exact Category.comp_id h
      map_comp := fun f g => by ext h; exact (Category.assoc h f g).symm

instance contentRepresentableFunctor_additive (v : ContentCategory D Sc cutoff N β) :
    (contentRepresentableFunctor D Sc cutoff N β v).Additive where
  map_add {w z} f g := by
    apply LinearMap.ext
    intro h
    exact Preadditive.comp_add v.obj w.obj z.obj h f g

instance contentRepresentableFunctor_linear (v : ContentCategory D Sc cutoff N β) :
    (contentRepresentableFunctor D Sc cutoff N β v).Linear k where
  map_smul {w z} f r := by
    apply LinearMap.ext
    intro h
    exact Linear.comp_smul v.obj w.obj z.obj h r f

instance contentRepresentableFunctor_super (v : ContentCategory D Sc cutoff N β) :
    IsSuperfunctor k (contentRepresentableFunctor D Sc cutoff N β v) where
    map_mem := by
      intro w z p f hf
      apply SVec.mem_parityHom_of_apply_mem
      intro q h hh
      change h ∈ (contentHomSpace D Sc cutoff N β v w).part q at hh
      change h ≫ f ∈ (contentHomSpace D Sc cutoff N β v z).part (q + p)
      rw [contentHomSpace_part] at hh ⊢
      exact comp_mem hh hf

def contentRepresentable (v : ContentCategory D Sc cutoff N β) :
    ContentModules D Sc cutoff N β := ⟨contentRepresentableFunctor D Sc cutoff N β v⟩

/-- Evaluation on actual source representables detects the coefficient family. -/
theorem contentRealize_injective : Function.Injective (contentRealize D Sc cutoff N β) := by
  intro c d h
  apply Superfunctor.hom_ext
  intro p v
  have he := congrArg (fun t => ((t.app p (contentRepresentable D Sc cutoff N β v)).app p v)
    (𝟙 v)) h
  change (𝟙 v ≫ (proj k p c).app p v) = (𝟙 v ≫ (proj k p d).app p v) at he
  simp only [Superfunctor.proj_app, ↓reduceIte] at he
  change 𝟙 v.obj ≫ c.app p v = 𝟙 v.obj ≫ d.app p v at he
  exact (Category.id_comp (c.app p v)).symm.trans (he.trans (Category.id_comp (d.app p v)))

end OddMath.QuiverHecke.ELVOld

import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossingTensor
import StringDiagrams.Super.BoxProduct

/-! # Actual supermodules on the full old ELV quotient category

The already proved old parity decomposition defines the supercategory
structure on the existing quotient category, with the established quotient
projections. Its source representables are actual superfunctors. These are
the untruncated coefficient modules needed to identify the prescribed
crossing source with induction of a parity-shifted restriction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

instance oldSupercategory : Supercategory k (OldCategory D Sc cutoff) where
  parity v w := oldParity D Sc cutoff v.word w.word
  isInternal v w := oldParity_internal D Sc cutoff v.word w.word
  id_mem v := Submodule.mem_map_of_mem (Supercategory.id_mem (obj D Sc cutoff v.word))
  comp_mem := by
    rintro v t w p q f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact Submodule.mem_map_of_mem (Supercategory.comp_mem ha hb)

theorem oldCategory_proj (v w : OldCategory D Sc cutoff)
    (p : ZMod 2) (f : v ⟶ w) :
    Supercategory.proj k p f = oldProj D Sc cutoff v.word w.word p f := by
  refine Supercategory.induction_on (R := k) f (by simp) (fun q f hf => ?_)
    (fun f g hf hg => by simp only [map_add, hf, hg])
  rw [oldProj_of_mem D Sc cutoff hf p]
  by_cases h : q = p
  · subst q
    rw [ite_eq_left rfl, Supercategory.proj_of_mem hf]
  · rw [ite_eq_right h, Supercategory.proj_of_mem_ne hf h]

def oldRepresentableFunctor (v : OldCategory D Sc cutoff) :
    OldCategory D Sc cutoff ⥤ SVec k where
  obj := Supercategory.homSVec k (OldCategory D Sc cutoff) v
  map f :=
    { toFun := fun h => h ≫ f
      map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun r h => Linear.smul_comp _ _ _ _ _ _ }
  map_id w := by ext h; exact Category.comp_id h
  map_comp f g := by ext h; exact (Category.assoc h f g).symm

instance oldRepresentableFunctor_additive (v : OldCategory D Sc cutoff) :
    (oldRepresentableFunctor D Sc cutoff v).Additive where
  map_add {w z} f g := by
    apply LinearMap.ext
    intro h
    exact Preadditive.comp_add v w z h f g

instance oldRepresentableFunctor_linear (v : OldCategory D Sc cutoff) :
    (oldRepresentableFunctor D Sc cutoff v).Linear k where
  map_smul {w z} f r := by
    apply LinearMap.ext
    intro h
    exact Linear.comp_smul v w z h r f

instance oldRepresentableFunctor_super (v : OldCategory D Sc cutoff) :
    IsSuperfunctor k (oldRepresentableFunctor D Sc cutoff v) where
  map_mem := by
    intro w z p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q h hh
    change h ∈ (Supercategory.homSVec k (OldCategory D Sc cutoff) v w).part q at hh
    change h ≫ f ∈ (Supercategory.homSVec k (OldCategory D Sc cutoff) v z).part (q + p)
    exact (Supercategory.mem_homSVec_part_iff k).2
      (comp_mem ((Supercategory.mem_homSVec_part_iff k).1 hh) hf)

def oldRepresentable (v : OldCategory D Sc cutoff) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨oldRepresentableFunctor D Sc cutoff v⟩

end OddMath.QuiverHecke.ELVOld

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Content-indexed ELV module induction and restriction

The exact-content full subcategories retain every quotient morphism, its
coefficient action and super parity. Right append changes content by multiset
addition. Balanced induction along this functor is left adjoint to restriction
on all supernatural module maps. This is the content-indexed module-category
step of `DeformedActionAssembly.md` §5; it does not assert factor normalization,
biadjunction, or the defining relations of the full categorical action.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The full truncated ELV category on words of exactly the specified content. -/
structure ContentCategory (β : Multiset I) where
  obj : TruncatedCategory D Sc cutoff N
  content : (obj.word : Multiset I) = β

instance contentCategory (β : Multiset I) : Category (ContentCategory D Sc cutoff N β) where
  Hom v w := v.obj ⟶ w.obj
  id v := 𝟙 v.obj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance contentPreadditive (β : Multiset I) : Preadditive (ContentCategory D Sc cutoff N β) where
  homGroup v w := inferInstanceAs (AddCommGroup (v.obj ⟶ w.obj))
  add_comp := by intro v w z f g h; exact Preadditive.add_comp v.obj w.obj z.obj f g h
  comp_add := by intro v w z f g h; exact Preadditive.comp_add v.obj w.obj z.obj f g h

instance contentLinear (β : Multiset I) : Linear k (ContentCategory D Sc cutoff N β) where
  homModule v w := inferInstanceAs (Module k (v.obj ⟶ w.obj))
  smul_comp := by intro v w z r f g; exact Linear.smul_comp v.obj w.obj z.obj r f g
  comp_smul := by intro v w z f r g; exact Linear.comp_smul v.obj w.obj z.obj f r g

instance contentSupercategory (β : Multiset I) :
    Supercategory k (ContentCategory D Sc cutoff N β) where
  parity v w := parity (R := k) v.obj w.obj
  isInternal v w := Supercategory.isInternal v.obj w.obj
  id_mem v := id_mem v.obj
  comp_mem := Supercategory.comp_mem

/-- Inclusion is the identity on the entire quotient Hom module. -/
def contentInclusion (β : Multiset I) :
    ContentCategory D Sc cutoff N β ⥤ TruncatedCategory D Sc cutoff N where
  obj v := v.obj
  map f := f

instance contentInclusion_full (β : Multiset I) : (contentInclusion D Sc cutoff N β).Full where
  map_surjective f := ⟨f, rfl⟩
instance contentInclusion_faithful (β : Multiset I) :
    (contentInclusion D Sc cutoff N β).Faithful where
  map_injective h := h

/-- Append between exact-content categories, with no restriction on colours. -/
def contentAppend (β : Multiset I) (σ : List I) :
    ContentCategory D Sc cutoff N β ⥤ ContentCategory D Sc cutoff N (β + (σ : Multiset I)) where
  obj v := ⟨(truncatedAppend D Sc cutoff N σ).obj v.obj, by
    change ((v.obj.word ++ σ : List I) : Multiset I) = _
    rw [← Multiset.coe_add, v.content]⟩
  map f := (truncatedAppend D Sc cutoff N σ).map f
  map_id v := (truncatedAppend D Sc cutoff N σ).map_id v.obj
  map_comp f g := (truncatedAppend D Sc cutoff N σ).map_comp f g

instance contentAppend_additive (β : Multiset I) (σ : List I) :
    (contentAppend D Sc cutoff N β σ).Additive where
  map_add := (truncatedAppend D Sc cutoff N σ).map_add
instance contentAppend_linear (β : Multiset I) (σ : List I) :
    (contentAppend D Sc cutoff N β σ).Linear k where
  map_smul f r := (truncatedAppend D Sc cutoff N σ).map_smul r f
instance contentAppend_super (β : Multiset I) (σ : List I) :
    IsSuperfunctor k (contentAppend D Sc cutoff N β σ) where
  map_mem := Supercategory.map_mem (truncatedAppend D Sc cutoff N σ)

/-- Integer grading is inherited independently of super parity. -/
@[instance_reducible]
def contentGradedSupercategory (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) : GradedSupercategory k (ContentCategory D Sc cutoff N β) := by
  letI := truncatedGradedSupercategory D Sc cutoff N sy hc
  exact
    { degree := fun v w => GradedSupercategory.degree (R := k) v.obj w.obj
      isInternal_degree := fun v w => GradedSupercategory.isInternal_degree v.obj w.obj
      proj_mem_degree := fun p hf => GradedSupercategory.proj_mem_degree p hf
      id_mem_degree := fun v => GradedSupercategory.id_mem_degree v.obj
      comp_mem_degree := fun hf hg => GradedSupercategory.comp_mem_degree hf hg }

/-- Right append preserves the inherited integer grading as well as parity. -/
def contentAppendGraded (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (σ : List I) :
    letI := contentGradedSupercategory D Sc cutoff N sy hc β
    letI := contentGradedSupercategory D Sc cutoff N sy hc (β + (σ : Multiset I))
    GradedSuperfunctor k (ContentCategory D Sc cutoff N β)
      (ContentCategory D Sc cutoff N (β + (σ : Multiset I))) := by
  letI := contentGradedSupercategory D Sc cutoff N sy hc β
  letI := contentGradedSupercategory D Sc cutoff N sy hc (β + (σ : Multiset I))
  exact { toFunctor := contentAppend D Sc cutoff N β σ
          isGraded := { map_mem_degree := fun hf =>
            truncatedAppend_mem_degree D Sc cutoff N sy hc σ hf } }

/-- All parity-graded modules and all supernatural maps at exact content. -/
abbrev ContentModules (β : Multiset I) :=
  Superfunctor k (ContentCategory D Sc cutoff N β) (SVec.{u} k)

/-- Balanced tensor induction from content `β` to content `β + σ`. -/
abbrev contentInduction (β : Multiset I) (σ : List I) :
    ContentModules D Sc cutoff N β ⥤ ContentModules D Sc cutoff N (β + (σ : Multiset I)) :=
  BalancedInduction.induction (contentAppend D Sc cutoff N β σ)

/-- Precomposition restriction from content `β + σ` to content `β`. -/
abbrev contentRestriction (β : Multiset I) (σ : List I) :
    ContentModules D Sc cutoff N (β + (σ : Multiset I)) ⥤ ContentModules D Sc cutoff N β :=
  BalancedInduction.restriction (contentAppend D Sc cutoff N β σ)

/-- The right adjoint of content induction is the constructed restriction functor. -/
def contentAdjunction (β : Multiset I) (σ : List I) :
    contentInduction D Sc cutoff N β σ ⊣ contentRestriction D Sc cutoff N β σ :=
  BalancedInduction.adjunction (contentAppend D Sc cutoff N β σ)

/-- The one-colour raising functor. -/
abbrev contentF (β : Multiset I) (i : I) := contentInduction D Sc cutoff N β [i]
/-- The one-colour lowering functor, with source content `β + {i}`. -/
abbrev contentE (β : Multiset I) (i : I) := contentRestriction D Sc cutoff N β [i]

/-- Right adjunction for the one-colour induction and restriction functors. -/
def contentFEAdjunction (β : Multiset I) (i : I) :
    contentF D Sc cutoff N β i ⊣ contentE D Sc cutoff N β i :=
  contentAdjunction D Sc cutoff N β [i]

end OddMath.QuiverHecke.ELVOld

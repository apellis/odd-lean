import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule

/-! # Untruncated old ELV categories of a fixed content
This restricts the existing old category, with its entire coefficient ring,
to a finite permutation class of words. Append is the existing canonical old
append functor. No coefficient truncation occurs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full old category on the finite permutation class of a word. -/
structure OldContentCategory (ν : List I) where
  obj : OldCategory D Sc cutoff
  wordPerm : obj.word.Perm ν

instance oldContentCategory (ν : List I) : Category (OldContentCategory D Sc cutoff ν) where
  Hom v w := v.obj ⟶ w.obj
  id v := 𝟙 v.obj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance oldContentPreadditive (ν : List I) : Preadditive (OldContentCategory D Sc cutoff ν) where
  homGroup v w := inferInstanceAs (AddCommGroup (v.obj ⟶ w.obj))
  add_comp := by intro v w z f g h; exact Preadditive.add_comp v.obj w.obj z.obj f g h
  comp_add := by intro v w z f g h; exact Preadditive.comp_add v.obj w.obj z.obj f g h

instance oldContentLinear (ν : List I) : Linear k (OldContentCategory D Sc cutoff ν) where
  homModule v w := inferInstanceAs (Module k (v.obj ⟶ w.obj))
  smul_comp := by intro v w z r f g; exact Linear.smul_comp v.obj w.obj z.obj r f g
  comp_smul := by intro v w z f r g; exact Linear.comp_smul v.obj w.obj z.obj f r g

instance oldContentSupercategory (ν : List I) :
    Supercategory k (OldContentCategory D Sc cutoff ν) where
  parity v w := parity (R := k) v.obj w.obj
  isInternal v w := Supercategory.isInternal v.obj w.obj
  id_mem v := id_mem v.obj
  comp_mem := Supercategory.comp_mem

/-- The inclusion preserves every quotient Hom, including exterior coefficients. -/
def oldContentInclusion (ν : List I) :
    OldContentCategory D Sc cutoff ν ⥤ OldCategory D Sc cutoff where
  obj v := v.obj
  map f := f

instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Full where
  map_surjective f := ⟨f,rfl⟩
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Faithful where
  map_injective h := h
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Additive where
  map_add := rfl
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Linear k where
  map_smul _ _ := rfl
instance (ν : List I) : IsSuperfunctor k (oldContentInclusion D Sc cutoff ν) where
  map_mem h := h

/-- Extract the same finite content coordinate from an actual content object. -/
def oldContentWord (ν : List I) (v : OldContentCategory D Sc cutoff ν) : ContentWords ν :=
  ⟨v.obj.word,v.wordPerm⟩

/-- Append uses the existing canonical untruncated old functor. -/
def oldContentAppend (ν : List I) (i : I) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff (i :: ν) where
  obj v := ⟨(CyclotomicCrossingTensor.append D Sc cutoff i).obj v.obj,
    (v.wordPerm.append (List.Perm.refl [i])).trans
      (List.perm_append_comm : (ν ++ [i]).Perm ([i] ++ ν))⟩
  map f := (CyclotomicCrossingTensor.append D Sc cutoff i).map f
  map_id v := (CyclotomicCrossingTensor.append D Sc cutoff i).map_id v.obj
  map_comp f g := (CyclotomicCrossingTensor.append D Sc cutoff i).map_comp f g

instance (ν : List I) (i : I) : (oldContentAppend D Sc cutoff ν i).Additive where
  map_add := (CyclotomicCrossingTensor.append D Sc cutoff i).map_add
instance (ν : List I) (i : I) : (oldContentAppend D Sc cutoff ν i).Linear k where
  map_smul f r := (CyclotomicCrossingTensor.append D Sc cutoff i).map_smul r f
instance (ν : List I) (i : I) : IsSuperfunctor k (oldContentAppend D Sc cutoff ν i) where
  map_mem := Supercategory.map_mem (CyclotomicCrossingTensor.append D Sc cutoff i)

/-- Appending then including is literally the established old append functor. -/
theorem oldContentAppend_inclusion (ν : List I) (i : I) :
    oldContentAppend D Sc cutoff ν i ⋙ oldContentInclusion D Sc cutoff (i :: ν) =
      oldContentInclusion D Sc cutoff ν ⋙ CyclotomicCrossingTensor.append D Sc cutoff i := rfl

end OddMath.QuiverHecke.ELVOld


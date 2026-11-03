/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentExtensionAppend

/-! # Old-content append with a prescribed target index

The mixed mate of Brundan–Ellis (1.12) uses a common upper content for the
two orders of append. This functor retains the literal old append on
objects and arrows while allowing any permutation of its content index.
The canonical full-content extension comparisons retain that append.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Append the given colour and retain a prescribed permutation of the target content. -/
def oldContentAppendTo (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff μ where
  obj v := ⟨((oldContentAppend D Sc cutoff ν i).obj v).obj,
    ((oldContentAppend D Sc cutoff ν i).obj v).wordPerm.trans h⟩
  map f := (CyclotomicCrossingTensor.append D Sc cutoff i).map f
  map_id v := (CyclotomicCrossingTensor.append D Sc cutoff i).map_id v.obj
  map_comp f g := (CyclotomicCrossingTensor.append D Sc cutoff i).map_comp f g

instance (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    (oldContentAppendTo D Sc cutoff ν i μ h).Additive where
  map_add := (CyclotomicCrossingTensor.append D Sc cutoff i).map_add
instance (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    (oldContentAppendTo D Sc cutoff ν i μ h).Linear k where
  map_smul f r := (CyclotomicCrossingTensor.append D Sc cutoff i).map_smul r f
instance (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    IsSuperfunctor k (oldContentAppendTo D Sc cutoff ν i μ h) where
  map_mem := Supercategory.map_mem (CyclotomicCrossingTensor.append D Sc cutoff i)

/-- Both orders of content indexing include into the identical old append functor. -/
theorem oldContentAppendTo_inclusion (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    oldContentAppendTo D Sc cutoff ν i μ h ⋙ oldContentInclusion D Sc cutoff μ =
      oldContentInclusion D Sc cutoff ν ⋙ CyclotomicCrossingTensor.append D Sc cutoff i := rfl

/-- The chosen append-extension comparison also applies to a prescribed target index. -/
def oldContentAppendToExtensionIso (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    BalancedInduction.induction (k := k) (oldContentAppendTo D Sc cutoff ν i μ h) ⋙
        BalancedInduction.induction (oldContentInclusion D Sc cutoff μ) ≅
      BalancedInduction.induction (oldContentInclusion D Sc cutoff ν) ⋙
        BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i) :=
  BalancedInduction.inductionComp (oldContentAppendTo D Sc cutoff ν i μ h)
      (oldContentInclusion D Sc cutoff μ) ≪≫
    BalancedInduction.inductionFunctorIsoOfEq _ _
      (oldContentAppendTo_inclusion D Sc cutoff ν i μ h) ≪≫
    (BalancedInduction.inductionComp (oldContentInclusion D Sc cutoff ν)
      (CyclotomicCrossingTensor.append D Sc cutoff i)).symm

end OddMath.QuiverHecke.ELVOld

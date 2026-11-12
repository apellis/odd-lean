/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAppendTo
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendMate

/-! # Permutation transport of the scalar-evaluated old probe

`SwappedDetectingFamily` §2: replacing a stored content list by a permutation
retains the literal old word objects, quotient arrows and coefficient action.
These equivalences permit canonical multiset representatives without changing
the probe algebra or imposing coefficient-power truncation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν μ η : List I}

/-- Reindex only the permutation certificate of an actual old word. -/
def oldContentReindex (h : ν.Perm μ) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff μ where
  obj v := ⟨v.obj, v.wordPerm.trans h⟩
  map f := f

instance (h : ν.Perm μ) : (oldContentReindex D Sc cutoff h).Additive where
  map_add := rfl
instance (h : ν.Perm μ) : (oldContentReindex D Sc cutoff h).Linear k where
  map_smul _ _ := rfl
instance (h : ν.Perm μ) : IsSuperfunctor k (oldContentReindex D Sc cutoff h) where
  map_mem hf := hf

@[simp] theorem oldContentReindex_comp (h : ν.Perm μ) (g : μ.Perm η) :
    oldContentReindex D Sc cutoff h ⋙ oldContentReindex D Sc cutoff g =
      oldContentReindex D Sc cutoff (h.trans g) := rfl

@[simp] theorem oldContentReindex_refl :
    oldContentReindex D Sc cutoff (List.Perm.refl ν) = 𝟭 _ := rfl

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ η : List I}

/-- Pullback along a representative change retains scalar evaluation. -/
theorem probeEvaluatesCoefficients_reindex (h : ν.Perm μ)
    (M : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) μ) (SVec k))
    (hM : ProbeEvaluatesCoefficients D m Sc μ M) :
    ProbeEvaluatesCoefficients D m Sc ν
      ((restriction (oldContentReindex D Sc (probeCutoff D m) h)).obj M) := by
  intro v c
  exact hM ((oldContentReindex D Sc (probeCutoff D m) h).obj v) c

/-- Transport an evaluated module to a new stored list, with unchanged vector spaces. -/
def probeEvaluatedReindex (h : ν.Perm μ) :
    ProbeEvaluatedModules D Sc m ν ⥤ ProbeEvaluatedModules D Sc m μ where
  obj M := ⟨(restriction (oldContentReindex D Sc (probeCutoff D m) h.symm)).obj M.obj,
    probeEvaluatesCoefficients_reindex D Sc m h.symm M.obj M.property⟩
  map f := ⟨(restriction (oldContentReindex D Sc (probeCutoff D m) h.symm)).map f.hom⟩
  map_id M := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_id M.obj)
  map_comp f g := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_comp f.hom g.hom)

instance (h : ν.Perm μ) : (probeEvaluatedReindex D Sc m h).Additive where
  map_add := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_add)
instance (h : ν.Perm μ) : (probeEvaluatedReindex D Sc m h).Linear k where
  map_smul f r := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_smul r f.hom)
instance (h : ν.Perm μ) : IsSuperfunctor k (probeEvaluatedReindex D Sc m h) where
  map_mem := by
    intro A B p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (restriction (oldContentReindex D Sc (probeCutoff D m) h.symm)).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf

@[simp] theorem probeEvaluatedReindex_comp (h : ν.Perm μ) (g : μ.Perm η) :
    probeEvaluatedReindex D Sc m h ⋙ probeEvaluatedReindex D Sc m g =
      probeEvaluatedReindex D Sc m (h.trans g) := rfl

@[simp] theorem probeEvaluatedReindex_refl :
    probeEvaluatedReindex D Sc m (List.Perm.refl ν) = 𝟭 _ := rfl

end OddMath.QuiverHecke

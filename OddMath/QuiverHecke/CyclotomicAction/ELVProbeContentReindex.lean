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

/-- Both representative changes include into the identical old category. -/
theorem oldContentReindex_inclusion (h : ν.Perm μ) :
    oldContentReindex D Sc cutoff h ⋙ oldContentInclusion D Sc cutoff μ =
      oldContentInclusion D Sc cutoff ν := rfl

/-- The representative change is an actual even equivalence. -/
def oldContentReindexEquivalence (h : ν.Perm μ) :
    OldContentCategory D Sc cutoff ν ≌ OldContentCategory D Sc cutoff μ where
  functor := oldContentReindex D Sc cutoff h
  inverse := oldContentReindex D Sc cutoff h.symm
  unitIso := eqToIso (by rfl)
  counitIso := eqToIso (by rfl)

/-- Retargeted old append is ordinary append followed by the certificate change. -/
theorem oldContentAppendTo_reindex (i : I) (h : (i :: ν).Perm μ) :
    oldContentAppendTo D Sc cutoff ν i μ h =
      oldContentAppend D Sc cutoff ν i ⋙ oldContentReindex D Sc cutoff h := rfl

/-- The two append squares have exactly the same quotient arrows. -/
theorem oldContentReindex_append (i : I) (h : ν.Perm μ) :
    oldContentReindex D Sc cutoff h ⋙ oldContentAppend D Sc cutoff μ i =
      oldContentAppend D Sc cutoff ν i ⋙ oldContentReindex D Sc cutoff (h.cons i) := rfl

/-- The chosen append dot is the same physical quotient arrow after reindexing. -/
theorem oldContentReindex_dot (i : I) (h : ν.Perm μ)
    (v : OldContentCategory D Sc cutoff ν) :
    (oldContentReindex D Sc cutoff (h.cons i)).map
        (oldContentAppendDot D Sc cutoff ν i v) =
      oldContentAppendDot D Sc cutoff μ i ((oldContentReindex D Sc cutoff h).obj v) := rfl

/-- Reindexing retains the literal positive equal-colour crossing. -/
theorem oldContentReindex_equalCross (i : I) (h : ν.Perm μ)
    (v : OldContentCategory D Sc cutoff ν) :
    (oldContentReindex D Sc cutoff ((h.cons i).cons i)).map
        (oldContentEqualCross D Sc cutoff ν i v) =
      oldContentEqualCross D Sc cutoff μ i ((oldContentReindex D Sc cutoff h).obj v) := rfl

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ η : List I}

/-- The full coefficient action is unchanged by a content representative change. -/
theorem probeOldCoefficient_reindex (h : ν.Perm μ)
    (v : OldContentCategory D Sc (probeCutoff D m) ν)
    (c : SKM.SYM.ELVCoefficientAlgebra (k := k) D (probeCutoff D m)) :
    (oldContentReindex D Sc (probeCutoff D m) h).map (probeOldCoefficient D m Sc ν v c) =
      probeOldCoefficient D m Sc μ ((oldContentReindex D Sc (probeCutoff D m) h).obj v) c := rfl

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

/-- The two scalar-evaluated full subcategories are equivalent through literal pullback. -/
def probeEvaluatedReindexEquivalence (h : ν.Perm μ) :
    ProbeEvaluatedModules D Sc m ν ≌ ProbeEvaluatedModules D Sc m μ where
  functor := probeEvaluatedReindex D Sc m h
  inverse := probeEvaluatedReindex D Sc m h.symm
  unitIso := eqToIso (by rfl)
  counitIso := eqToIso (by rfl)

/-- Restriction commutes strictly with the chosen representative transport. -/
theorem probeEvaluatedReindex_restriction (i : I) (h : ν.Perm μ) :
    probeEvaluatedReindex D Sc m (h.cons i) ⋙ probeEvaluatedRestriction D Sc m μ i =
      probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedReindex D Sc m h := rfl

end OddMath.QuiverHecke

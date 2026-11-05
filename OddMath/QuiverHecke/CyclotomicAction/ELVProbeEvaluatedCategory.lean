/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldInductionDotInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals

/-! # The scalar-evaluated old probe module category

`SwappedNondegeneracy` §3 and `SwappedDetectingFamily` §2 use the prescribed
scalar specialization of the full ELV probe factor. Its full module
subcategory is stable under the actual append induction and restriction,
parity, and module products. The target retains all module morphisms;
no assertion is made about arbitrary unevaluated old modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
private theorem comp_scalar_action
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (S : Superfunctor k (SVec k) (SVec k))
    (v : C) (f : v ⟶ v) (r : k) (h : M.toFunctor.map f = r • 𝟙 (M.obj v)) :
    (M.comp S).toFunctor.map f = r • 𝟙 ((M.comp S).obj v) := by
  change S.toFunctor.map (M.toFunctor.map f) = _
  rw [h, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)

/-- All old probe modules with the prescribed full scalar coefficient action;
all even and odd module morphisms are retained. -/
abbrev ProbeEvaluatedModules :=
  ObjectProperty.FullSubcategory (ProbeEvaluatesCoefficients D m Sc ν)

/-- The specified old append induction stays inside the scalar specialization. -/
def probeEvaluatedInduction (i : I) :
    ProbeEvaluatedModules D Sc m ν ⥤ ProbeEvaluatedModules D Sc m (i :: ν) where
  obj N := ⟨induced (oldContentAppend D Sc (probeCutoff D m) ν i) N.obj,
    probeOldInduced_evaluatesCoefficients D m Sc ν i N.obj N.property⟩
  map f := ⟨(induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom⟩
  map_id N := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_id N.obj)
  map_comp f g := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_comp f.hom g.hom)

/-- The specified old restriction stays inside the same scalar specialization. -/
def probeEvaluatedRestriction (i : I) :
    ProbeEvaluatedModules D Sc m (i :: ν) ⥤ ProbeEvaluatedModules D Sc m ν where
  obj N := ⟨(restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).obj N.obj,
    probeOldRestriction_evaluatesCoefficients D Sc m ν i N.obj N.property⟩
  map f := ⟨(restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom⟩
  map_id N := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_id N.obj)
  map_comp f g := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_comp f.hom g.hom)

instance probeEvaluatedInduction_additive (i : I) : (probeEvaluatedInduction D Sc m ν i).Additive where
  map_add := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_add)
instance probeEvaluatedInduction_linear (i : I) : (probeEvaluatedInduction D Sc m ν i).Linear k where
  map_smul f r := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_smul r f.hom)
instance probeEvaluatedInduction_super (i : I) : IsSuperfunctor k (probeEvaluatedInduction D Sc m ν i) where
  map_mem := by
    intro A B p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf
instance probeEvaluatedRestriction_additive (i : I) : (probeEvaluatedRestriction D Sc m ν i).Additive where
  map_add := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_add)
instance probeEvaluatedRestriction_linear (i : I) : (probeEvaluatedRestriction D Sc m ν i).Linear k where
  map_smul f r := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_smul r f.hom)
instance probeEvaluatedRestriction_super (i : I) : IsSuperfunctor k (probeEvaluatedRestriction D Sc m ν i) where
  map_mem := by
    intro A B p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf

/-- Scalar evaluation is stable under the actual vector parity functor. -/
theorem probeEvaluatesCoefficients_parity
    (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc ν (supermoduleParityObj N) := by
  intro v c
  exact comp_scalar_action N (PiSCat.piHom (PiSCat.of k (SVec k))) v
    (probeOldCoefficient D m Sc ν v c) _ (hN v c)

/-- The actual scalar-evaluated probe category has its inherited parity completion. -/
@[instance_reducible]
def probeEvaluatedPiSupercategory : PiSupercategory k (ProbeEvaluatedModules D Sc m ν) :=
  letI := supermodulePiSupercategory (k := k) (C := OldContentCategory D Sc (probeCutoff D m) ν)
  CyclotomicAction.fullPiSupercategory (ProbeEvaluatesCoefficients D m Sc ν)
    (probeEvaluatesCoefficients_parity D Sc m ν)

end OddMath.QuiverHecke

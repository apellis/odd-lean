import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexPair
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeReindexPairConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private theorem hp : ([false,true] : List Bool).Perm [true,false] :=
  List.Perm.swap _ _ _
private theorem lower (i : Bool) : (i :: [false,true]).Perm (i :: [false,true]) :=
  List.Perm.refl _
private theorem upper (i : Bool) :
    (i :: [true,false]).Perm ((i :: [true,false] : List Bool) : Multiset Bool).toList :=
  probeCanonicalRepresentative _
private theorem pair (i : Bool) :
    (i :: [false,true]).Perm ((i :: [true,false] : List Bool) : Multiset Bool).toList :=
  (hp.cons i).trans (upper i)

private abbrev n₁ (i : Bool) := i :: [false,true]
private abbrev c₁ (i : Bool) := ((i :: [true,false] : List Bool) : Multiset Bool).toList
private abbrev n₂ (i j : Bool) := j :: n₁ i
private abbrev c₂ (i j : Bool) := ((j :: c₁ i : List Bool) : Multiset Bool).toList
private theorem lower₂ (i j : Bool) : (j :: n₁ i).Perm (n₂ i j) := List.Perm.refl _
private theorem upper₂ (i j : Bool) : (j :: c₁ i).Perm (c₂ i j) := probeCanonicalRepresentative _
private theorem pair₂ (i j : Bool) : (n₂ i j).Perm (c₂ i j) :=
  ((pair i).cons j).trans (upper₂ i j)

example (i j : Bool) := oldAppendPairReindexIso_hom D Sc cut hp i j (lower i) (upper i) (pair i)
  (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true]).obj
example (i j : Bool) := oldAppendPairReindexIso_hom_mem D Sc cut hp i j (lower i) (upper i) (pair i)
  (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true]).obj
example (i j : Bool) (w : OldContentCategory D Sc cut (c₂ i j)) :=
  oldAppendPairReindexLinear_comp D Sc cut hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true]).obj w

example (i j : Bool) (s : OldContentCategory D Sc cut [false,true])
    (t : OldContentCategory D Sc cut (n₁ i)) (w : OldContentCategory D Sc cut (c₂ i j))
    (a : (oldContentAppendTo D Sc cut [false,true] i (n₁ i) (lower i)).obj s ⟶ t)
    (g : (oldContentAppendTo D Sc cut (n₁ i) j (n₂ i j) (lower₂ i j)).obj t ⟶
      (oldContentReindex D Sc cut (pair₂ i j).symm).obj w)
    (b : (N [false,true]).obj.obj s) :=
  oldAppendPairReindexIso_hom_tensor D Sc cut hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true]).obj s t w a g b

example (i j : Bool) :=
  probeAppendPairReindexIso_hom_native D Sc m hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true])
example (i j : Bool) :=
  probeAppendPairReindexIso_inv_native D Sc m hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true])
example (i j : Bool) :=
  probeAppendPairReindexIso_hom_mem D Sc m hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true])
example (i j : Bool) (w : OldContentCategory D Sc cut (c₂ i j)) :=
  probeAppendPairReindexIso_hom_linear D Sc m hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j) (N [false,true]) w

private def shifted : ProbeEvaluatedModules D Sc m [false,true] :=
  ⟨supermoduleParityObj (N [false,true]).obj,
    probeEvaluatesCoefficients_parity D Sc m [false,true] (N [false,true]).obj
      (N [false,true]).property⟩
private def oddInput : shifted ⟶ N [false,true] :=
  ⟨(supermoduleParityIso (N [false,true]).obj).hom⟩
example (i j : Bool) :=
  (oldAppendPairReindexIso D Sc cut hp i j (lower i) (upper i) (pair i)
    (lower₂ i j) (upper₂ i j) (pair₂ i j)).hom.naturality oddInput.hom
end ProbeReindexPairConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexPair
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

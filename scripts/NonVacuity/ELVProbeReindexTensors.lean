import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeReindexTensorsConsumer
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

example (i : Bool) := oldAppendReindexLeftAdjunction_unit D Sc cut i (lower i) (pair i)
  (N [false,true]).obj
example (i : Bool) := oldAppendReindexRightAdjunction_unit D Sc cut hp i (lower i) (upper i) (pair i)
  (N [false,true]).obj
example (i : Bool) (s : OldContentCategory D Sc cut [false,true])
    (b : (N [false,true]).obj.obj s) :=
  oldAppendReindexIso_hom_unit D Sc cut hp i (lower i) (upper i) (pair i)
    (N [false,true]).obj s b

example (i : Bool) (s : OldContentCategory D Sc cut [false,true])
    (w : OldContentCategory D Sc cut ((i :: [true,false] : List Bool) : Multiset Bool).toList)
    (g : (oldContentAppendTo D Sc cut [false,true] i (i :: [false,true]) (lower i)).obj s ⟶
      (oldContentReindex D Sc cut (pair i).symm).obj w)
    (b : (N [false,true]).obj.obj s) :=
  oldAppendReindexIso_hom_tensor D Sc cut hp i (lower i) (upper i) (pair i)
    (N [false,true]).obj s w g b

example (i : Bool)
    (w : OldContentCategory D Sc cut ((i :: [true,false] : List Bool) : Multiset Bool).toList) :=
  probeAppendReindexIso_hom_linear D Sc m hp i (lower i) (upper i) (pair i) (N [false,true]) w
private def shifted : ProbeEvaluatedModules D Sc m [false,true] :=
  ⟨supermoduleParityObj (N [false,true]).obj,
    probeEvaluatesCoefficients_parity D Sc m [false,true] (N [false,true]).obj
      (N [false,true]).property⟩
private def oddInput : shifted ⟶ N [false,true] :=
  ⟨(supermoduleParityIso (N [false,true]).obj).hom⟩
example (i : Bool) := (probeAppendReindexIso D Sc m hp i (lower i) (upper i) (pair i)).hom.naturality
  oddInput
end ProbeReindexTensorsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexTensors
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

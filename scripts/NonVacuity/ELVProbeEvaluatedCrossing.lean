import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCrossing
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeEvaluatedCrossingConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def shifted (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨supermoduleParityObj (N ν).obj,
    probeEvaluatesCoefficients_parity D Sc m ν (N ν).obj (N ν).property⟩
private def oddInput (ν : List Bool) : shifted ν ⟶ N ν :=
  ⟨(supermoduleParityIso (N ν).obj).hom⟩
private theorem oddInput_mem (ν : List Bool) : oddInput ν ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem (N ν).obj

example (i : Bool) := probeEvaluatedEqualCross_mem D Sc m [false,true] i
example (i : Bool) (q : ZMod 2) :=
  probeEvaluatedEqualCross_native_app D Sc m [false,true] i q (N [false,true])
example (i : Bool) := probeEvaluatedEqualCross_total D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedEqualCross_native_total D Sc m [false,true] i (N [false,true])
example (i : Bool) := (probeEvaluatedEqualCrossComponent_supernatural D Sc m [false,true] i).naturality
  (oddInput_mem [false,true])
example (i : Bool) := probeEvaluatedEqualCrossComponent_naturality_twist D Sc m [false,true] i
  (oddInput [false,true])
example (i : Bool) := probeEvaluatedEqualCross_square D Sc m [false,true] i
example (i : Bool) := probeEvaluatedEqualCross_total D Sc m [] i (N [])
example (i : Bool) := probeEvaluatedEqualCross_native_total D Sc m [] i (N [])
example (i : Bool) := probeEvaluatedEqualCross_square D Sc m [] i
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeEvaluatedCrossingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

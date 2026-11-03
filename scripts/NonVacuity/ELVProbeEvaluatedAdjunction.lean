import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedAdjunction
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeEvaluatedAdjunctionConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
example (i : Bool) := probeEvaluatedRightAdjunction D Sc m [false,true] i
example (i : Bool) := probeEvaluatedAdjunction_unit_mem D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedAdjunction_counit_mem D Sc m [false,true] i (N (i :: [false,true]))
example (i : Bool) := probeEvaluatedUnit_native D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedCounit_native D Sc m [false,true] i (N (i :: [false,true]))
example (i : Bool) := probeEvaluatedInductionDot_native_total D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedRightAdjunction D Sc m [] i
example (i : Bool) := probeEvaluatedUnit_native D Sc m [] i (N [])
example (i : Bool) := probeEvaluatedCounit_native D Sc m [] i (N [i])
example (i : Bool) := probeEvaluatedInductionDot_native_total D Sc m [] i (N [])
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeEvaluatedAdjunctionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedAdjunction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

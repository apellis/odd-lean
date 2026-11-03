import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDotUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeEvaluatedDotUnitConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
example (i : Bool) := probeEvaluatedInductionDot_isUnit D Sc m [false,true] i
example (i : Bool) := probeEvaluatedInductionDotIso_inv_mem D Sc m [false,true] i
example (i : Bool) := probeEvaluatedInductionDotIso_hom D Sc m [false,true] i
example (i : Bool) := probeEvaluatedInductionDot_total D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedDotModuleIso_hom D Sc m [false,true] i (N [false,true])
example (i : Bool) := (probeEvaluatedInductionDotIso D Sc m [false,true] i).hom_inv_id
example (i : Bool) := (probeEvaluatedInductionDotIso D Sc m [false,true] i).inv_hom_id
example (i : Bool) := probeEvaluatedInductionDot_isUnit D Sc m [] i
example (i : Bool) := probeEvaluatedInductionDotIso_inv_mem D Sc m [] i
example (i : Bool) := probeEvaluatedInductionDot_total D Sc m [] i (N [])
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeEvaluatedDotUnitConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDotUnit
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedBraid
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeEvaluatedBraidConsumer
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

example (i : Bool) := probeEvaluatedEqualCross_braid D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedEqualCross_braid D Sc m [false,true] i (shifted [false,true])
example (i : Bool) := probeEvaluatedEqualCross_braid D Sc m [] i (N [])
example (i : Bool) := probeEvaluatedBraidPrefix_total D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedBraidSuffix_total D Sc m [false,true] i (N [false,true])
example (i : Bool) := probeEvaluatedBraid D Sc m [false,true] i
example (i : Bool) := probeEvaluatedBraid D Sc m [] i
example (i : Bool) := ((probeEvaluatedBraidPrefix D Sc m [false,true] i).isSupernatural (D.parity i)).naturality
  (oddInput_mem [false,true])
example (i : Bool) := ((probeEvaluatedBraidSuffix D Sc m [false,true] i).isSupernatural (D.parity i)).naturality
  (oddInput_mem [false,true])
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeEvaluatedBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

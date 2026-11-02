import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCounitComparison
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ELVProbeCounitComparisonConsumer

private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private def M3 := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) 3)
private def N3 (i : Bool) := probeOldModule D m Sc (i :: ν) M3
private abbrev hN3 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (i :: ν) M3

/-- Both moving parities retain the chosen counit on every output word. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeAppendOrdinaryCounitLinear_eq D Sc m ν i (N3 i) (hN3 i) w

private def M1 := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N1 (i : Bool) := probeOldModule D m Sc [i] M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] M1

/-- The same ordinary counit identity includes vacuum source content. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) :=
  probeAppendOrdinaryCounitLinear_eq D Sc m [] i (N1 i) (hN1 i) w

end ELVProbeCounitComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCounitComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."

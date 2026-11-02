import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ELVProbeRestrictionComparisonConsumer

private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private def M3 := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) 3)
private def N3 (i : Bool) := probeOldModule D m Sc (i :: ν) M3
private abbrev hN3 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (i :: ν) M3

/-- Both moving parities use actual mixed-content scalar probe modules. -/
example (i : Bool) :=
  probeOldRestriction_evaluatesCoefficients D Sc m ν i (N3 i) (hN3 i)

example (i : Bool) :=
  probeOrdinaryRestrictionModule_eq D Sc m ν i (N3 i) (hN3 i)

example (i : Bool) (p : ZMod 2) (v : OrdinaryContentCategory D Sc a ν) :=
  probeRestrictionEqToHom_app D Sc m ν i (N3 i) (hN3 i) p v

private def M1 := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N1 (i : Bool) := probeOldModule D m Sc [i] M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] M1

/-- Restriction from one strand includes the empty source content. -/
example (i : Bool) :=
  probeOldRestriction_evaluatesCoefficients D Sc m [] i (N1 i) (hN1 i)

example (i : Bool) :=
  probeOrdinaryRestrictionModule_eq D Sc m [] i (N1 i) (hN1 i)

end ELVProbeRestrictionComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."

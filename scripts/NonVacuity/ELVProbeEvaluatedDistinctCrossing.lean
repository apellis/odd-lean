import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctCrossing
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeEvaluatedDistinctCrossingConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

example (i : Bool) := probeEvaluatedDistinctCross_mem D Sc m [false,true] i (!i)
example (i : Bool) (q : ZMod 2) := probeEvaluatedDistinctCross_native_app D Sc m [false,true]
  i (!i) q (N [false,true])
example (i : Bool) := probeEvaluatedDistinctRectangularMate_eq D Sc m [false,true] i (!i)
example (i : Bool) := probeEvaluatedDistinctRectangularMate_isIso D Sc m [false,true]
  i (!i) (distinct i)
example (i : Bool) := probeEvaluatedDistinctRectangularMate_isIso D Sc m [] i (!i) (distinct i)

private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private abbrev ao : Bool → Polynomial ℚ := probePolynomial (probeDotExponent Do) m
private def Ro := SuperBimodule.regular
  (heightParity Do So ao (probePolynomial_parity Do m) 0)
private def No : ProbeEvaluatedModules Do So m [] :=
  ⟨probeOldModule Do m So [] Ro, probeOldModule_evaluatesCoefficients Do m So [] Ro⟩
private def shifted : ProbeEvaluatedModules Do So m [] :=
  ⟨supermoduleParityObj No.obj,
    probeEvaluatesCoefficients_parity Do So m [] No.obj No.property⟩
private def oddInput : shifted ⟶ No := ⟨(supermoduleParityIso No.obj).hom⟩
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem No.obj

/-- Distinct odd colours retain crossing parity and its odd-input naturality. -/
example := probeEvaluatedDistinctCross_mem Do So m [] false true
example := (probeEvaluatedDistinctCross Do So m [] false true).naturality 1 oddInput oddInput_mem
example := probeEvaluatedDistinctRectangularMate_eq Do So m [] false true
example := probeEvaluatedDistinctRectangularMate_isIso Do So m [] false true (by decide)
end ProbeEvaluatedDistinctCrossingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

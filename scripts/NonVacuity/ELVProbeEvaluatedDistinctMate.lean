import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctMate
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
namespace ProbeEvaluatedDistinctMateConsumer
private abbrev D := ELVOld.WeightedAppendFixture.datum
private abbrev Sc := ELVOld.WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

example (i : Bool) := probeEvaluatedDistinctMate_mem D Sc m [false,true] i (!i)
example (i : Bool) := probeEvaluatedDistinctMate_total D Sc m [false,true] i (!i)
  (N ((!i) :: [false,true]))
example (i : Bool) := probeEvaluatedDistinctMateModuleIso_hom D Sc m [false,true] i (!i)
  (distinct i) (N ((!i) :: [false,true]))
example (i : Bool) := probeEvaluatedDistinctMateModuleIso_inv_native D Sc m [false,true] i (!i)
  (distinct i) (N ((!i) :: [false,true]))
example (i : Bool) := (probeEvaluatedDistinctMateIso D Sc m [] i (!i) (distinct i)).hom_inv_id
example (i : Bool) := (probeEvaluatedDistinctMateIso D Sc m [] i (!i) (distinct i)).inv_hom_id

private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private abbrev ao : Bool → Polynomial ℚ := probePolynomial (probeDotExponent Do) m
private def Ro := SuperBimodule.regular
  (heightParity Do So ao (probePolynomial_parity Do m) 1)
private def No : ProbeEvaluatedModules Do So m [true] :=
  ⟨probeOldModule Do m So [true] Ro, probeOldModule_evaluatesCoefficients Do m So [true] Ro⟩
private def shifted : ProbeEvaluatedModules Do So m [true] :=
  ⟨supermoduleParityObj No.obj,
    probeEvaluatesCoefficients_parity Do So m [true] No.obj No.property⟩
private def oddInput : shifted ⟶ No := ⟨(supermoduleParityIso No.obj).hom⟩
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem No.obj

/-- Distinct odd colours retain an odd forward and inverse on the actual probe. -/
example := probeEvaluatedDistinctMateModuleIso_hom Do So m [] false true (by decide) No
example := probeEvaluatedDistinctMateIso_inv_mem Do So m [] false true (by decide)
example := (probeEvaluatedDistinctMateIso Do So m [] false true (by decide)).hom_inv_id
example := (probeEvaluatedDistinctMateIso Do So m [] false true (by decide)).inv_hom_id
example := (probeEvaluatedDistinctMateIso Do So m [] false true (by decide)).hom.naturality 1
  oddInput oddInput_mem
example := (probeEvaluatedDistinctMateIso Do So m [] false true (by decide)).inv.naturality 1
  oddInput oddInput_mem
end ProbeEvaluatedDistinctMateConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

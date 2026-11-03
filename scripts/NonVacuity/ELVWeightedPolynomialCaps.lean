import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPolynomialCaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVWeightedPolynomialCaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def plusSecond : Module.End ℚ AQ :=
  weightedPolynomialCapMoment D Sc cutoff L false (positive false) 2 1
private def minusSecond : Module.End ℚ AQ :=
  weightedCapMomentLinear D Sc cutoff L false (positive false) 1
    ((weightedModuleDot D Sc cutoff L false ^ 2 - 1) ^ 2)
-- Proposed snapshot: actual nonpositive first closures and the occupied
-- second-closure plus/minus comparison are added after producer identities.
end NonVacuity.ELVWeightedPolynomialCaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPolynomialCaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"

import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightTripleCrossCoordinatesConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def W (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β => N β.1.toList
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩

example (i j l : Bool) := probeOldWeightCrossPrefix_total D Sc m i j l Λ
  rfl rfl rfl (by abel) rfl (W (w [l,!l,j]))
  (probeOldBlockSucc₃ D i j l Λ rfl rfl rfl (base [l,!l,j]))
example (i j l : Bool) := probeOldWeightCrossPrefix_via_total D Sc m i j l Λ
  rfl rfl rfl (by abel) rfl (base [l,!l,j]) _ _ _ _ rfl rfl rfl
  (blockSucc_comm D Λ j l rfl rfl rfl (by abel) (base [l,!l,j])).symm rfl
  (W (w [l,!l,j]))
example (i j l : Bool) := probeOldWeightCrossSuffix_total D Sc m i j l Λ
  rfl rfl rfl rfl (by abel) (W (w [l,!l,j]))
  (probeOldBlockSucc₃ D i j l Λ rfl rfl rfl (base [l,!l,j]))
example (i j l : Bool) := probeOldWeightCrossSuffix_via_total D Sc m i j l Λ
  rfl rfl rfl rfl (by abel) (base [l,!l,j]) _ _ _ _ rfl rfl rfl rfl
  (blockSucc_comm D Λ i j rfl rfl rfl (by abel)
    (blockSucc D Λ l rfl (base [l,!l,j]))).symm
  (W (w [l,!l,j]))
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)
private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private abbrev ao : Bool → Polynomial ℚ := probePolynomial (probeDotExponent Do) m
private def Ro (ν : List Bool) := SuperBimodule.regular
  (heightParity Do So ao (probePolynomial_parity Do m) ν.length)
private def No (ν : List Bool) : ProbeEvaluatedModules Do So m ν :=
  ⟨probeOldModule Do m So ν (Ro ν), probeOldModule_evaluatesCoefficients Do m So ν (Ro ν)⟩
private def Wo (x : Bool → ℤ) : ProbeOldWeightProduct Do So m Λ x := fun β => No β.1.toList
private def bo : WeightBlocks Do Λ (-Λ) := ⟨0, by simp⟩
example (i j l : Bool) := probeOldWeightCrossPrefix_via_total Do So m i j l Λ
  rfl rfl rfl (by abel) rfl bo _ _ _ _ rfl rfl rfl
  (blockSucc_comm Do Λ j l rfl rfl rfl (by abel) bo).symm rfl (Wo (-Λ))
example (i j l : Bool) := probeOldWeightCrossSuffix_via_total Do So m i j l Λ
  rfl rfl rfl rfl (by abel) bo _ _ _ _ rfl rfl rfl rfl
  (blockSucc_comm Do Λ i j rfl rfl rfl (by abel) (blockSucc Do Λ l rfl bo)).symm (Wo (-Λ))
example (i : Bool) : probeOldVacuumAppendVector Do So m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero Do So m i (by cases i <;> decide)
end ProbeWeightTripleCrossCoordinatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleCrossCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

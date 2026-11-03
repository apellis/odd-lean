import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightCrossCoordinatesConsumer
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

example (i : Bool) := probeOldBlockEqualCross_stored_total D Sc m i Λ rfl rfl (base [i,!i])
  (W (w [i,!i]) (base [i,!i]))
example (i j : Bool) := probeOldBlockDistinctCross_stored_total D Sc m i j Λ
  rfl rfl rfl (by abel) (base [i,!i]) _ rfl (W (w [i,!i]) (base [i,!i]))
example (i : Bool) := probeOldActionEqualCross_eq_neg_distinct D Sc m i Λ
  (a := w [i,!i]) rfl rfl
example (i j : Bool) := probeOldActionCross_eq_normalized_distinct D Sc m i j Λ
  (a := w [i,!i]) rfl rfl rfl (by abel)
example (i j : Bool) := probeOldActionCross_stored_total D Sc m i j Λ
  rfl rfl rfl (by abel) (base [i,!i]) _ rfl (W (w [i,!i]))
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
example (i : Bool) := probeOldActionEqualCross_eq_neg_distinct Do So m i Λ (a := -Λ) rfl rfl
example (i j : Bool) := probeOldActionCross_eq_normalized_distinct Do So m i j Λ
  (a := -Λ) rfl rfl rfl (by abel)
example (i j : Bool) := probeOldActionCross_stored_total Do So m i j Λ
  rfl rfl rfl (by abel) bo _ rfl (Wo (-Λ))
example (i : Bool) : probeOldVacuumAppendVector Do So m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero Do So m i (by cases i <;> decide)
end ProbeWeightCrossCoordinatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCrossCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

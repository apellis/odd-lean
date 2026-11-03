import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightSupportedInverse
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightSupportedInverseConsumer
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

private theorem negHeight (i : Bool) : D.h i (w [] + D.α i) ≤ 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum, AsymmetricParameters.datum,
    SKM.Datum.h, SKM.Datum.α, probeCutoff, probeDotExponent, m]
private theorem posHeight (i : Bool) : 0 ≤ D.h i (w (List.replicate 6 i) + D.α i) := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum, AsymmetricParameters.datum,
    SKM.Datum.h, SKM.Datum.α, probeCutoff, probeDotExponent, m]
example (i : Bool) := probeOldWeightSupportedUnitInverse_nonempty D Sc m i Λ
  rfl rfl (base []) rfl (negHeight i) (W (w [] + D.α i))
example (i : Bool) := probeOldWeightSupportedCapInverse_nonempty D Sc m i Λ
  rfl rfl (base (List.replicate 6 i)) rfl (posHeight i) (W (w (List.replicate 6 i) + D.α i))

namespace ZeroHeight
private def m : Bool → ℕ := fun i => if i then 1 else 2
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def W (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β => N β.1.toList
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem zeroHeight (i : Bool) : D.h i (w [] + D.α i) = 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum, AsymmetricParameters.datum,
    SKM.Datum.h, SKM.Datum.α, probeCutoff, probeDotExponent, m]
example (i : Bool) := probeOldWeightSupportedUnitInverse_nonempty D Sc m i Λ
  rfl rfl (base []) rfl (by rw [zeroHeight]) (W (w [] + D.α i))
example (i : Bool) := probeOldWeightSupportedCapInverse_nonempty D Sc m i Λ
  rfl rfl (base []) rfl (by rw [zeroHeight]) (W (w [] + D.α i))
end ZeroHeight
end ProbeWeightSupportedInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightSupportedInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

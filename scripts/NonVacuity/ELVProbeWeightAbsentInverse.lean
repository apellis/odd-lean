import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAbsentInverse
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightAbsentInverseConsumer
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
private theorem diff (i : Bool) : i ≠ !i := by cases i <;> decide

private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem absent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (show (-Λ - D.α i) + D.α i = -Λ by abel) β = emptyBlock := by
  rintro ⟨β, hβ⟩
  have h := congrArg (fun γ => γ.1.card) hβ
  simp only [blockSucc_val, Multiset.card_add, Multiset.card_singleton,
    emptyBlock, Multiset.card_zero] at h
  omega
example (i : Bool) := probeOldWeightAbsentUnitInverse_nonempty D Sc m i Λ
  (x₀ := -Λ - D.α i) (x₁ := -Λ) (by abel) rfl emptyBlock rfl (absent i) (W (-Λ))
namespace Zero
private def m : Bool → ℕ := fun _ => 0
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def W (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β => N β.1.toList
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem absent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (show (-Λ - D.α i) + D.α i = -Λ by abel) β = emptyBlock := by
  rintro ⟨β, hβ⟩
  have h := congrArg (fun γ => γ.1.card) hβ
  simp only [blockSucc_val, Multiset.card_add, Multiset.card_singleton,
    emptyBlock, Multiset.card_zero] at h
  omega
private theorem zeroHeight (i : Bool) : D.h i (-Λ) = 0 := by
  change -(probeCutoff D m i : ℤ) = 0
  simp only [probeCutoff, m, mul_zero, Nat.cast_zero, neg_zero]
example (i : Bool) := probeOldWeightAbsentUnitInverse_nonempty D Sc m i Λ
  (x₀ := -Λ - D.α i) (x₁ := -Λ) (by abel) rfl emptyBlock rfl (absent i) (W (-Λ))
example (i : Bool) := probeOldWeightAbsentCapInverse_nonempty D Sc m i Λ
  (x₀ := -Λ - D.α i) (x₁ := -Λ) (by abel) rfl emptyBlock rfl (absent i)
  (by rw [zeroHeight]) (W (-Λ))
end Zero
end ProbeWeightAbsentInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAbsentInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

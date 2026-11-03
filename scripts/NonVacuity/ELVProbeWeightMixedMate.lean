import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMate
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightMixedMateConsumer
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

example (i : Bool) := probeOldWeightMixedMate_mem D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl
example (i : Bool) (p : ZMod 2) := probeOldWeightMixedMate_app D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl p (W (w [] + D.α (!i)))
example (i : Bool) (p : ZMod 2) := probeOldWeightMixedMate_app_block D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl p (W (w [] + D.α (!i))) (blockSucc D Λ i rfl (base []))

private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem absent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (show (-Λ - D.α i) + D.α i = -Λ by abel) β = emptyBlock := by
  rintro ⟨β, hβ⟩
  have h := congrArg (fun γ => γ.1.card) hβ
  simp only [blockSucc_val, Multiset.card_add, Multiset.card_singleton,
    emptyBlock, Multiset.card_zero] at h
  omega
example (i : Bool) (p : ZMod 2) := probeOldWeightMixedMate_absent_isIso D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i) (xi := -Λ) rfl (by abel) (by abel) rfl
  (diff i) emptyBlock (absent i) p (W ((-Λ - D.α i) + D.α (!i)))
example (i : Bool) := probeOldWeightMixedSource_isZero D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i) (xi := -Λ) rfl (by abel) emptyBlock (absent i)
  (W ((-Λ - D.α i) + D.α (!i)))
example (i : Bool) := probeOldWeightMixedTarget_isZero D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i) (xi := -Λ) (by abel) (by abel) rfl (diff i) emptyBlock (absent i)
  (W ((-Λ - D.α i) + D.α (!i)))
end ProbeWeightMixedMateConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

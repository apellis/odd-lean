import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLocalMateCoordinates
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightLocalMateCoordinatesConsumer
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

example (i : Bool) := probeOldWeightRouquierMate_mem D Sc m i Λ (x₀ := w []) rfl rfl
example (i : Bool) := probeOldBlockEqualCross_stored_eq D Sc m i Λ
  rfl rfl (base [])
example (i : Bool) (p : ZMod 2) := probeOldWeightRouquierMate_comparison D Sc m i Λ
  rfl rfl (base []) p (W (w [] + D.α i))
private def shifted (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β =>
  ⟨supermoduleParityObj (W x β).obj,
    probeEvaluatesCoefficients_parity D Sc m β.1.toList (W x β).obj (W x β).property⟩
private def oddInput (x : Bool → ℤ) : shifted x ⟶ W x := fun β =>
  ⟨(supermoduleParityIso (W x β).obj).hom⟩
private theorem oddInput_mem (x : Bool → ℤ) : oddInput x ∈ parity (R := ℚ) _ _ 1 := by
  intro β
  exact supermoduleParityIso_hom_mem (W x β).obj
example (i : Bool) (p : ZMod 2) := probeOldWeightRouquierMate_comparison D Sc m i Λ
  rfl rfl (base []) p (shifted (w [] + D.α i))
example := oddInput_mem (w [])
end ProbeWeightLocalMateCoordinatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLocalMateCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

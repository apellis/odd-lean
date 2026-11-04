import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctReservoirShift
import StringDiagrams.Super.DrinfeldCenterPiCounterexample
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
open OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.DistinctReservoirShift
private abbrev B := TwoEnvelope ℚ (UnitTwo ℚ)
private def o : B := ⟨UnitTwo.pt⟩
private def e (p : ZMod 2) : o ⟶ o := ⟨p, ⟨⟩⟩
private def χ : e 0 ≫ e 0 ⟶ e 1 ≫ e 0 := Envelope.ofHom (1 : ℚ)
private theorem χ_odd : χ ∈ parity (R := ℚ) _ _ 1 := by
  rw [Envelope.mem_parity_iff]
  change (1 : ℚ) ∈ trivialGrading ℚ (0 : ZMod 2)
  simp
example := postPairCrossing_eq (k := ℚ) 0 1 χ χ_odd (e 0)
example := postPairCrossing_eq (k := ℚ) 1 0 χ χ_odd (e 0)
example : sign ℚ (((1 : ZMod 2) + 0) * 1) = -1 := by decide
example : χ ≠ 0 := by
  intro h
  have h' := congrArg Envelope.toHom h
  change (1 : ℚ) = 0 at h'
  norm_num at h'
end NonVacuity.DistinctReservoirShift
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctReservoirShift
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
namespace OldAppendCrossingConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private theorem odd_square : D.parity false * D.parity false = 1 := by decide
private abbrev M := oldRepresentable D Sc cutoff (⟨[false, true]⟩ : OldCategory D Sc cutoff)
example : IsSupernatural ℚ 1
    (F := (append D Sc cutoff false) ⋙ (append D Sc cutoff false))
    (G := (append D Sc cutoff false) ⋙ (append D Sc cutoff false))
    (equalCrossComponent D Sc cutoff false) := by
  simpa only [odd_square] using equalCross_supernatural D Sc cutoff false
example : signedEqualInductionCross D Sc cutoff false ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [odd_square] using signedEqualInductionCross_mem D Sc cutoff false
example : (signedEqualInductionCross D Sc cutoff false).app 1 M =
    -equalCrossOnDoubleInduction D Sc cutoff false M := by
  simpa only [odd_square, ↓reduceIte] using signedEqualInductionCross_app D Sc cutoff false 1 M
end OldAppendCrossingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"

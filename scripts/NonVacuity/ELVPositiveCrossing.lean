import NonVacuity.ELVCoefficientCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVPositiveCrossing
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.QuiverHecke ELVOld CyclotomicCrossingTensor
open ELVCoefficientCategoryConsumer

/-- Odd rank-one crossing with its actual two-term polynomial window. -/
def positiveWindowCrossing :
    (Source datum scalars (fun _ => 4) () [()] [()] ×
      boundaryRowWindow datum scalars (fun _ => 4) oddColour [()]) ≃ₗ[ℚ]
      Old datum scalars (fun _ => 4) [(), ()] [(), ()] := by
  apply positiveCrossingEquiv datum scalars (fun _ => 4) 0 oddColour [()]
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 4) () [()]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, oddColour] at h ⊢ <;> omega

example (z : Source datum scalars (fun _ => 4) () [()] [()] ×
    boundaryRowWindow datum scalars (fun _ => 4) oddColour [()]) :
    positiveWindowCrossing.symm (positiveWindowCrossing z) = z :=
  positiveWindowCrossing.symm_apply_apply z

example (z : Old datum scalars (fun _ => 4) [(), ()] [(), ()]) :
    positiveWindowCrossing (positiveWindowCrossing.symm z) = z :=
  positiveWindowCrossing.apply_symm_apply z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPositiveCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"

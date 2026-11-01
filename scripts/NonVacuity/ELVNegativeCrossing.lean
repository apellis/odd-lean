import NonVacuity.ELVCoefficientCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVNegativeCrossing
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.QuiverHecke ELVOld CyclotomicCrossingTensor
open ELVCoefficientCategoryConsumer

/-- Odd rank one, full exterior coefficients, and one actual contraction row. -/
def negativeRawCrossing :
    Source datum scalars (fun _ => 1) () [()] [()] ≃ₗ[ℚ]
      (Old datum scalars (fun _ => 1) [(), ()] [(), ()] ×
        (Fin 1 → Old datum scalars (fun _ => 1) [()] [()])) := by
  apply negativeCrossingEquiv datum scalars (fun _ => 1) 0 oddColour [()] 1
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 1) () [()]
  norm_num [datum] at h
  omega

example (z : Source datum scalars (fun _ => 1) () [()] [()]) :
    negativeRawCrossing.symm (negativeRawCrossing z) = z :=
  negativeRawCrossing.symm_apply_apply z

example (z : Old datum scalars (fun _ => 1) [(), ()] [(), ()] ×
    (Fin 1 → Old datum scalars (fun _ => 1) [()] [()])) :
    negativeRawCrossing (negativeRawCrossing.symm z) = z :=
  negativeRawCrossing.apply_symm_apply z

/-- The empty cap window includes height zero. -/
def zeroRawCrossing :
    Source datum scalars (fun _ => 2) () [()] [()] ≃ₗ[ℚ]
      (Old datum scalars (fun _ => 2) [(), ()] [(), ()] ×
        (Fin 0 → Old datum scalars (fun _ => 2) [()] [()])) := by
  apply negativeCrossingEquiv datum scalars (fun _ => 2) 0 oddColour [()] 0
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 2) () [()]
  norm_num [datum] at h
  omega

example (z : Source datum scalars (fun _ => 2) () [()] [()]) :
    zeroRawCrossing.symm (zeroRawCrossing z) = z :=
  zeroRawCrossing.symm_apply_apply z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.Algebra.FiniteTriangularCoordinates,
    `OddMath.QuiverHecke.CyclotomicAction.ELVNegativeCrossing]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}, including private helpers"

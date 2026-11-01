import NonVacuity.ELVCoefficientCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundarySnake
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.QuiverHecke ELVOld CyclotomicCrossingTensor
open ELVCoefficientCategoryConsumer

/-- The actual crossing kernel at negative KKO height has the corrected low window. -/
def negativeCrossingKernel :
    boundaryKernelWindow datum scalars (fun _ => 1) oddColour [()] ≃ₗ[ℚ]
      LinearMap.ker (toCyclotomic datum scalars (fun _ => 1) () [()] [()]) :=
  (boundaryKernelEquiv datum scalars (fun _ => 1) 0 oddColour [()]).trans
    (boundarySnakeKernelEquiv datum scalars (fun _ => 1) 0 oddColour [()])

example (f : boundaryKernelWindow datum scalars (fun _ => 1) oddColour [()]) :
    negativeCrossingKernel.symm (negativeCrossingKernel f) = f :=
  negativeCrossingKernel.symm_apply_apply f

example (z : LinearMap.ker (toCyclotomic datum scalars (fun _ => 1) () [()] [()])) :
    negativeCrossingKernel (negativeCrossingKernel.symm z) = z :=
  negativeCrossingKernel.apply_symm_apply z

example (f : LinearMap.ker (outputPolynomialBoundary datum scalars (fun _ => 1) 0 oddColour [()])) :
    toCyclotomic datum scalars (fun _ => 1) () [()] [()]
      (boundarySnake datum scalars (fun _ => 1) 0 oddColour [()] f) = 0 :=
  toCyclotomic_boundarySnake datum scalars (fun _ => 1) 0 oddColour [()] f

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundarySnake
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"

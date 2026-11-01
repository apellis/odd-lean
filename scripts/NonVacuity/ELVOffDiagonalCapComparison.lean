import NonVacuity.ELVOffDiagonalInputMatrix
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCapComparison
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalCapComparisonConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer OffDiagonalInputMatrixConsumer

def shiftedMatrix : Input ≃ₗ[ℚ] (Output × (Fin 3 → Coeff)) :=
  offDiagonalShiftedInputMatrixEquiv datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 3 deepHeight

example (z : Input) : shiftedMatrix.symm (shiftedMatrix z) = z :=
  shiftedMatrix.symm_apply_apply z

example (z : Output × (Fin 3 → Coeff)) : shiftedMatrix (shiftedMatrix.symm z) = z :=
  shiftedMatrix.apply_symm_apply z

example (z : Input) :
    actualSourceInputContraction datum scalars deepCutoff movingOdd sourceWord targetWord z =
      offDiagonalInputContraction datum scalars deepCutoff movingOdd sourceWord targetWord z :=
  LinearMap.congr_fun (sourceInputContraction_eq datum scalars deepCutoff movingOdd sourceWord targetWord) z

example (z : Input) :
    actualSourceInputDot datum scalars deepCutoff movingOdd sourceWord targetWord z =
      offDiagonalCrossingInputDot datum scalars deepCutoff movingOdd sourceWord targetWord z :=
  LinearMap.congr_fun (sourceInputDot_eq datum scalars deepCutoff movingOdd sourceWord targetWord) z

end OffDiagonalCapComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCapComparison,
    `OddMath.QuiverHecke.CyclotomicAction.ELVActualCapInput,
    `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientModule]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"


import NonVacuity.ELVOffDiagonalBoundarySnake
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalActualCapPivots
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalCapConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer

theorem mixedPivotHeight :
    outputSDegree datum true [true, true, false] =
      0 + 0 + 1 + endpointQPDegree datum (fun _ => 1) true [true, true, false] := by
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 1) true [true, true, false]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum] at h ⊢
  omega

example (b : Old datum scalars (fun _ => 1) [true, true, false] [false, true, true]) :
    actualSourceInputContraction datum scalars (fun _ => 1) movingOdd
      [true, true, false] [false, true, true]
      ((actualSourceInputDot datum scalars (fun _ => 1) movingOdd
        [true, true, false] [false, true, true])^[0]
        (offDiagonalBoundaryCoordinates datum scalars (fun _ => 1) 0 movingOdd
          [true, true, false] [false, true, true]
          (offDiagonalLongExtraction datum scalars (fun _ => 1) 0 true
            [true, true, false] [false, true, true]
            (offDiagonalCorrectedLift datum scalars (fun _ => 1) 0 movingOdd
              [true, true, false] [false, true, true] 0 b)))) =
      offDiagonalBoundaryLeadingEquiv datum scalars (fun _ => 1) 0 movingOdd
        [true, true, false] [false, true, true] 0 b :=
  actualSourceInputContraction_corrected_pivot datum scalars (fun _ => 1) 0 movingOdd
    [true, true, false] [false, true, true] 0 0 b mixedPivotHeight

example (r : hom datum scalars (fun _ => 1) [true, true, false] ([true, false] ++ [true]))
    (g : hom datum scalars (fun _ => 1) ([true, false] ++ [true]) [false, true, true]) :
    actualSourceInputDot datum scalars (fun _ => 1) movingOdd
      [true, true, false] [false, true, true]
      (q datum scalars (fun _ => 1) true [true, true, false] [false, true, true]
        (shortTensor datum scalars (fun _ => 1) true [true, true, false] [true, false]
          [false, true, true] g ((ideal datum scalars (fun _ => 1) _ _).mkQ r))) =
    q datum scalars (fun _ => 1) true [true, true, false] [false, true, true]
      (offDiagonalInputDotAffine datum scalars (fun _ => 1) movingOdd
        [true, true, false] [false, true, true]
        (shortTensor datum scalars (fun _ => 1) true [true, true, false] [true, false]
          [false, true, true] g ((ideal datum scalars (fun _ => 1) _ _).mkQ r))) :=
  actualSourceInputDot_q datum scalars (fun _ => 1) movingOdd
    [true, true, false] [false, true, true] _

end OffDiagonalCapConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalActualCapPivots
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"

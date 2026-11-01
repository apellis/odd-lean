import NonVacuity.ELVOffDiagonalActualCapPivots
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalNegativeCrossing
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalNegativeConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer OffDiagonalCapConsumer

theorem mixedNegativeHeightOne :
    outputSDegree datum true [true, true, false] =
      endpointQPDegree datum (fun _ => 1) true [true, true, false] + 1 := by
  have h := mixedPivotHeight
  omega

/-- Actual counit/dot rows on different old words of the same mixed content. -/
def mixedNegative :
    Source datum scalars (fun _ => 1) true [true, true, false] [false, true, true] ≃ₗ[ℚ]
      (Old datum scalars (fun _ => 1) ([true, true, false] ++ [true])
        ([false, true, true] ++ [true]) ×
      (Fin 1 → Old datum scalars (fun _ => 1) [true, true, false] [false, true, true])) :=
  offDiagonalNegativeCrossingEquiv datum scalars (fun _ => 1) 0 movingOdd
    [true, true, false] [false, true, true] 1 mixedNegativeHeightOne

example (z : Source datum scalars (fun _ => 1) true [true, true, false] [false, true, true]) :
    mixedNegative.symm (mixedNegative z) = z := mixedNegative.symm_apply_apply z

example (z : Old datum scalars (fun _ => 1) ([true, true, false] ++ [true])
    ([false, true, true] ++ [true]) ×
    (Fin 1 → Old datum scalars (fun _ => 1) [true, true, false] [false, true, true])) :
    mixedNegative (mixedNegative.symm z) = z := mixedNegative.apply_symm_apply z

theorem mixedZeroHeight :
    outputSDegree datum true [true, false] =
      endpointQPDegree datum (fun _ => 0) true [true, false] + 0 := by
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 0) true [true, false]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum] at h ⊢
  omega

def mixedZero :
    Source datum scalars (fun _ => 0) true [true, false] [false, true] ≃ₗ[ℚ]
      (Old datum scalars (fun _ => 0) ([true, false] ++ [true]) ([false, true] ++ [true]) ×
      (Fin 0 → Old datum scalars (fun _ => 0) [true, false] [false, true])) :=
  offDiagonalNegativeCrossingEquiv datum scalars (fun _ => 0) 0 movingOdd
    [true, false] [false, true] 0 mixedZeroHeight

example (z : Source datum scalars (fun _ => 0) true [true, false] [false, true]) :
    mixedZero.symm (mixedZero z) = z := mixedZero.symm_apply_apply z

example (z : Old datum scalars (fun _ => 0) ([true, false] ++ [true]) ([false, true] ++ [true]) ×
    (Fin 0 → Old datum scalars (fun _ => 0) [true, false] [false, true])) :
    mixedZero (mixedZero.symm z) = z := mixedZero.apply_symm_apply z

end OffDiagonalNegativeConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalNegativeCrossing,
    `OddMath.Algebra.FiniteTriangularCoordinates]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"

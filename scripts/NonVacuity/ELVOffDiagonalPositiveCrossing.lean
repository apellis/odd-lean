import NonVacuity.ELVOffDiagonalRowSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalPositiveCrossing
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalPositiveConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer

def mixedPositive :
    (Source datum scalars (fun _ => 3) true [true, false] [false, true] ×
      offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]) ≃ₗ[ℚ]
      Old datum scalars (fun _ => 3) ([true, false] ++ [true]) ([false, true] ++ [true]) :=
  offDiagonalPositiveCrossingEquiv datum scalars (fun _ => 3) 0 movingOdd
    [true, false] [false, true] mixedPositiveHeight

example (z : Source datum scalars (fun _ => 3) true [true, false] [false, true] ×
    offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]) :
    mixedPositive.symm (mixedPositive z) = z := mixedPositive.symm_apply_apply z

example (z : Old datum scalars (fun _ => 3) ([true, false] ++ [true]) ([false, true] ++ [true])) :
    mixedPositive (mixedPositive.symm z) = z := mixedPositive.apply_symm_apply z

example (s : Source datum scalars (fun _ => 3) true [true, false] [false, true])
    (r : offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]) :
    mixedPositive (s, r) =
      toCyclotomic datum scalars (fun _ => 3) true [true, false] [false, true] s +
      canonicalAppendTarget datum scalars (fun _ => 3) true [true, false] ([false, true] ++ [true])
        (appendOutputEmbedding datum scalars (fun _ => 3) true [true, false] [false, true] r) := rfl

end OffDiagonalPositiveConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalPositiveCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"


import NonVacuity.ELVOffDiagonalRowSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundarySnake
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalSnakeConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer

def mixedSource :
    Target datum scalars (fun _ => 3) true [true, false] ([false, true] ++ [true]) ≃ₗ[ℚ]
      (PprimeDomain datum scalars (fun _ => 3) true [true, false] [false, true] ×
        (ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true])) :=
  offDiagonalSourceCoordinateEquiv datum scalars (fun _ => 3) 0 true [true, false] [false, true]

example (z : Target datum scalars (fun _ => 3) true [true, false] ([false, true] ++ [true])) :
    mixedSource.symm (mixedSource z) = z := mixedSource.symm_apply_apply z

example (a : PprimeDomain datum scalars (fun _ => 3) true [true, false] [false, true] ×
    (ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true])) :
    mixedSource (mixedSource.symm a) = a := mixedSource.apply_symm_apply a

example : Function.Injective (toCyclotomic datum scalars (fun _ => 3) true
    [true, false] [false, true]) :=
  offDiagonalToCyclotomic_injective_of_nonnegative_height datum scalars (fun _ => 3)
    0 movingOdd [true, false] [false, true] mixedPositiveHeight

example : Function.Surjective (toCyclotomic datum scalars (fun _ => 1) true
    [true, true, false] [false, true, true]) :=
  offDiagonalToCyclotomic_surjective_of_nonpositive_height datum scalars (fun _ => 1)
    0 movingOdd [true, true, false] [false, true, true] mixedNegativeHeight

def mixedSnake :
    LinearMap.ker (offDiagonalPolynomialBoundary datum scalars (fun _ => 1) 0 true
      [true, true, false] [false, true, true]) ≃ₗ[ℚ]
    LinearMap.ker (toCyclotomic datum scalars (fun _ => 1) true
      [true, true, false] [false, true, true]) :=
  offDiagonalBoundarySnakeKernelEquiv datum scalars (fun _ => 1) 0 movingOdd
    [true, true, false] [false, true, true]

example (f : LinearMap.ker (offDiagonalPolynomialBoundary datum scalars (fun _ => 1) 0 true
    [true, true, false] [false, true, true])) :
    mixedSnake.symm (mixedSnake f) = f := mixedSnake.symm_apply_apply f

example (z : LinearMap.ker (toCyclotomic datum scalars (fun _ => 1) true
    [true, true, false] [false, true, true])) :
    mixedSnake (mixedSnake.symm z) = z := mixedSnake.apply_symm_apply z

end OffDiagonalSnakeConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalSourceSplitting,
    `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCrossingHeight,
    `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundarySnake]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"

import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryKernel
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace EvenCrossingHeightConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num



example : Function.Injective (toCyclotomic mixedDatum mixedScalars (fun _ => 4) false [] []) :=
  evenToCyclotomic_injective_of_nonnegative_height mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [] [] (by norm_num [endpointQPDegree, outputSDegree])

example : Function.Surjective
    (toCyclotomic mixedDatum mixedScalars (fun _ => 1) false [false, false] [false, false]) :=
  evenToCyclotomic_surjective_of_nonpositive_height mixedDatum mixedScalars (fun _ => 1)
    1 false rfl [false, false] [false, false]
      (by norm_num [endpointQPDegree, outputSDegree, appendQPDegree, mixedDatum, List.range_succ, List.getD])

def zeroCrossing : Source mixedDatum mixedScalars (fun _ => 2) false [false] [false] ≃ₗ[ℚ]
    Old mixedDatum mixedScalars (fun _ => 2) ([false] ++ [false]) ([false] ++ [false]) :=
  evenToCyclotomicEquiv_zero_height mixedDatum mixedScalars (fun _ => 2) 1 false rfl
    [false] [false]
      (by norm_num [endpointQPDegree, outputSDegree, appendQPDegree, mixedDatum, List.range_succ, List.getD])

example (z : Source mixedDatum mixedScalars (fun _ => 2) false [false] [false]) :
    zeroCrossing.symm (zeroCrossing z) = z := zeroCrossing.symm_apply_apply z

example (z : Old mixedDatum mixedScalars (fun _ => 2) ([false] ++ [false]) ([false] ++ [false])) :
    zeroCrossing (zeroCrossing.symm z) = z := zeroCrossing.apply_symm_apply z

example : LinearMap.range
    (offDiagonalBoundarySnake mixedDatum mixedScalars (fun _ => 4) 1 false
      [false, true] [true, false]) =
    LinearMap.ker (toCyclotomic mixedDatum mixedScalars (fun _ => 4) false
      [false, true] [true, false]) :=
  offDiagonalRange_boundarySnake mixedDatum mixedScalars (fun _ => 4) 1 false
    [false, true] [true, false]

example (f : LinearMap.ker
    (offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false
      [false, true] [true, false])) :
    (offDiagonalBoundarySnakeKernelEquiv mixedDatum mixedScalars (fun _ => 4) 1 false
      [false, true] [true, false]).symm
      (offDiagonalBoundarySnakeKernelEquiv mixedDatum mixedScalars (fun _ => 4) 1 false
        [false, true] [true, false] f) = f := LinearEquiv.symm_apply_apply _ f

example (f : evenBoundaryKernelWindow mixedDatum mixedScalars (fun _ => 1) false
    [false, false] [false, false]) :
    (evenCrossingKernelEquiv mixedDatum mixedScalars (fun _ => 1) 1 false rfl
      [false, false] [false, false]).symm
      (evenCrossingKernelEquiv mixedDatum mixedScalars (fun _ => 1) 1 false rfl
        [false, false] [false, false] f) = f := LinearEquiv.symm_apply_apply _ f

example : evenBoundaryKernelWindow mixedDatum mixedScalars (fun _ => 1) false
      [false, false] [false, false] =
    Finsupp.supported (Old mixedDatum mixedScalars (fun _ => 1)
      [false, false] [false, false]) ℚ (Set.Iio 3) :=
  evenBoundaryKernelWindow_eq_height mixedDatum mixedScalars (fun _ => 1) false
    [false, false] [false, false] 3
    (by norm_num [endpointQPDegree, outputSDegree, appendQPDegree, mixedDatum, List.range_succ, List.getD])

example (f : evenBoundaryKernelWindow mixedDatum mixedScalars (fun _ => 1) false
    [false, false] [false, false]) :
    (evenCrossingKernelEquiv mixedDatum mixedScalars (fun _ => 1) 1 false rfl
      [false, false] [false, false] f).val =
    q mixedDatum mixedScalars (fun _ => 1) false [false, false] [false, false]
      (ShortCrossCoordinates.decode mixedDatum mixedScalars (fun _ => 1) false
        [false, false] [false, false]
        (pMap mixedDatum mixedScalars (fun _ => 1) false [false, false] ([false, false] ++ [false])
          (offDiagonalLongSection mixedDatum mixedScalars (fun _ => 1) 1 false
            [false, false] [false, false] f.val))) :=
  evenCrossingKernelEquiv_lift mixedDatum mixedScalars (fun _ => 1) 1 false rfl
    [false, false] [false, false] f

end EvenCrossingHeightConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryKernel,
      `OddMath.QuiverHecke.CyclotomicAction.ELVEvenCrossingHeight,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundarySnake] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} declarations of {owner}"

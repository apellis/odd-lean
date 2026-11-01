import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputPivots
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenInputPivotsConsumer
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

open CyclotomicCrossingTensor

/-- Negative height one instantiates the cap pivot on the prescribed Source. -/
example (b : Old mixedDatum mixedScalars (fun _ => 1) [true, false, false] [false, true, false]) :
    evenInputContraction mixedDatum mixedScalars (fun _ => 1) false rfl
      [true, false, false] [false, true, false]
      ((evenCrossingInputDot mixedDatum mixedScalars (fun _ => 1) false rfl
        [true, false, false] [false, true, false])^[0]
        (q mixedDatum mixedScalars (fun _ => 1) false [true, false, false] [false, true, false]
          (evenBoundaryCrossCoordinates mixedDatum mixedScalars (fun _ => 1) 1 false
            [true, false, false] [false, true, false] (Finsupp.single 0 b)))) =
    evenOffDiagonalBoundaryLeadingEquiv mixedDatum mixedScalars (fun _ => 1) 1 false
      [true, false, false] [false, true, false] b := by
  apply evenInputContraction_pivot mixedDatum mixedScalars (fun _ => 1) 1 false rfl
    [true, false, false] [false, true, false] 0 0 b
  norm_num [endpointQPDegree, appendQPDegree, outputSDegree, List.range_succ, List.getD,
    SKM.Datum.dn, SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum]

example (b : Old mixedDatum mixedScalars (fun _ => 1)
    [true, false, false, false] [false, true, false, false]) :
    evenInputContraction mixedDatum mixedScalars (fun _ => 1) false rfl
      [true, false, false, false] [false, true, false, false]
      ((evenCrossingInputDot mixedDatum mixedScalars (fun _ => 1) false rfl
        [true, false, false, false] [false, true, false, false])^[0]
        (q mixedDatum mixedScalars (fun _ => 1) false
          [true, false, false, false] [false, true, false, false]
          (evenBoundaryCrossCoordinates mixedDatum mixedScalars (fun _ => 1) 1 false
            [true, false, false, false] [false, true, false, false] (Finsupp.single 0 b)))) = 0 := by
  apply evenInputContraction_below mixedDatum mixedScalars (fun _ => 1) 1 false rfl
    [true, false, false, false] [false, true, false, false] 0 0 b
  norm_num [endpointQPDegree, appendQPDegree, outputSDegree, List.range_succ, List.getD,
    SKM.Datum.dn, SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum]

example (r d : ℕ)
    (b : Old mixedDatum mixedScalars (fun _ => 1) [true, false, false] [false, true, false]) :
    evenInputContraction mixedDatum mixedScalars (fun _ => 1) false rfl
      [true, false, false] [false, true, false]
      ((evenCrossingInputDot mixedDatum mixedScalars (fun _ => 1) false rfl
        [true, false, false] [false, true, false])^[r]
        (q mixedDatum mixedScalars (fun _ => 1) false [true, false, false] [false, true, false]
          (evenBoundaryCrossCoordinates mixedDatum mixedScalars (fun _ => 1) 1 false
            [true, false, false] [false, true, false] (Finsupp.single d b)))) =
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 1) 1 false
      [true, false, false] [false, true, false] (Finsupp.single (r + d + 1) b) 0 :=
  evenInputContraction_iterate_boundaryCrossCoordinates mixedDatum mixedScalars (fun _ => 1)
    1 false rfl [true, false, false] [false, true, false] r d b
end EvenInputPivotsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputPivots
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"


import OddMath.QuiverHecke.CyclotomicAction.ELVEvenPolynomialBoundary
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenPolynomialBoundaryConsumer
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

/-- The independent-S law is instantiated on connected mixed-parity data. -/
example (d : ℕ) :
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [false, true]
      ((evenLongShift mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true])^[d]
        (independentOutputS mixedDatum mixedScalars (fun _ => 4) false [false, true])) =
    appendC0 mixedDatum mixedScalars (fun _ => 4) false [false, true] [false, true]
      (appendProjection mixedDatum mixedScalars (fun _ => 4) false [false, true] [false, true, false]
        (appendMovingPower mixedDatum mixedScalars (fun _ => 4) false [false, true] d ≫
          affineUnit mixedDatum mixedScalars (fun _ => 4) _ _
            (appendQPProduct mixedDatum mixedScalars false [false, true]) ≫
          endpointELV mixedDatum mixedScalars (fun _ => 4) false [false, true])) :=
  offDiagonalPolynomialBoundary_even_independentS mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [false, true] d

example (z : Target mixedDatum mixedScalars (fun _ => 4) false [false, true] [false, true, false]) :
    offDiagonalLongExtraction mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [false, true] z =
    outputLongExtraction mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] z :=
  offDiagonalLongExtraction_diagonal mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] z

example (f : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]) :
    offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 true [false, true] [false, true] f =
    outputLongSection mixedDatum mixedScalars (fun _ => 4) 1 true [false, true] f :=
  offDiagonalLongSection_diagonal mixedDatum mixedScalars (fun _ => 4) 1 true [false, true] f

end EvenPolynomialBoundaryConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenPolynomialBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

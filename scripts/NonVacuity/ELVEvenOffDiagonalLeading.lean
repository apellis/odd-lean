import OddMath.QuiverHecke.CyclotomicAction.ELVEvenOffDiagonalLeading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenOffDiagonalLeadingConsumer
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

/-- Reversed old words keep their complete old Hom coefficient. -/
example (b : Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]) :
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false]
      (Finsupp.single (outputSDegree mixedDatum false [false, true]) b)
      (endpointQPDegree mixedDatum (fun _ => 4) false [false, true]) =
    evenOffDiagonalBoundaryLeadingEquiv mixedDatum mixedScalars (fun _ => 4)
      1 false [false, true] [true, false] b :=
  offDiagonalBoundary_even_top mixedDatum mixedScalars (fun _ => 4) 1 false rfl
    [false, true] [true, false] _ _ b (by omega)

example (b : Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]) (d n : ℕ) :
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false]
      (Finsupp.single d b) n =
    oldComp mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true] [true, false]
      (evenBoundaryPhi mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] d n)
      (oldTwist mixedDatum mixedScalars (fun _ => 4) 1 [false, true] [true, false] b) :=
  offDiagonalBoundary_even_coefficient mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [false, true] [true, false] d n b

/-- The equivalence includes an empty old Hom, with no supplied basis index. -/
example (b : Old mixedDatum mixedScalars (fun _ => 4) [] [true]) :
    (evenOffDiagonalBoundaryLeadingEquiv mixedDatum mixedScalars (fun _ => 4) 1 false [] [true]).symm
      (evenOffDiagonalBoundaryLeadingEquiv mixedDatum mixedScalars (fun _ => 4) 1 false [] [true] b) = b :=
  LinearEquiv.symm_apply_apply _ b
end EvenOffDiagonalLeadingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenOffDiagonalLeading
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

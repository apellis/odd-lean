import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRhoExtraction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

private def oddColour : {i : Bool // datum.parity i = 1} := ⟨false, rfl⟩

/-- Every class is allowed; no hypothesis restricts z to the selected long section. -/
example (z : Target datum scalars (fun _ => 12) oddColour.1 [false, true] ([true, false] ++ [oddColour.1])) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 1 oddColour.1 [false, true] [true, false]
      (boundaryRho datum scalars (fun _ => 12) oddColour [false, true] ([true, false] ++ [oddColour.1]) z) =
    offDiagonalCoefficientRho datum scalars (fun _ => 12) 1 oddColour [false, true] [true, false]
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 1 oddColour.1 [false, true] [true, false] z) :=
  offDiagonalLongExtraction_boundaryRho datum scalars (fun _ => 12) 1 oddColour [false, true] [true, false] z

example (z : Target datum scalars (fun _ => 12) oddColour.1 [] ([true] ++ [oddColour.1])) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 0 oddColour.1 [] [true]
      (boundaryRho datum scalars (fun _ => 12) oddColour [] ([true] ++ [oddColour.1]) z) =
    offDiagonalCoefficientRho datum scalars (fun _ => 12) 0 oddColour [] [true]
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 0 oddColour.1 [] [true] z) :=
  offDiagonalLongExtraction_boundaryRho datum scalars (fun _ => 12) 0 oddColour [] [true] z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRhoExtraction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

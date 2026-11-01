import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRhoExtraction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

private def oddColour : {i : Bool // datum.parity i = 1} := ⟨false, rfl⟩

/-- Every class is allowed; no hypothesis restricts z to the selected long section. -/
example (z : Target datum scalars (fun _ => 12) false [false, true] ([true, false] ++ [false])) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 1 false [false, true] [true, false]
      (boundaryRho datum scalars (fun _ => 12) oddColour [false, true] ([true, false] ++ [false]) z) =
    offDiagonalCoefficientRho datum scalars (fun _ => 12) 1 oddColour [false, true] [true, false]
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 1 false [false, true] [true, false] z) :=
  offDiagonalLongExtraction_boundaryRho datum scalars (fun _ => 12) 1 oddColour _ _ z

example (z : Target datum scalars (fun _ => 12) false [] [true, false]) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 0 false [] [true]
      (boundaryRho datum scalars (fun _ => 12) oddColour [] [true, false] z) =
    offDiagonalCoefficientRho datum scalars (fun _ => 12) 0 oddColour [] [true]
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 0 false [] [true] z) :=
  offDiagonalLongExtraction_boundaryRho datum scalars (fun _ => 12) 0 oddColour _ _ z

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

import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRho
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

private def oddColour : {i : Bool // datum.parity i = 1} := ⟨false, rfl⟩

/-- Both old endpoints occur in the actual corrected source operator. -/
example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    boundaryRho datum scalars (fun _ => 12) oddColour [false, true] ([true, false] ++ [false])
      (offDiagonalLongSection datum scalars (fun _ => 12) 1 false [false, true] [true, false] f) =
    offDiagonalLongSection datum scalars (fun _ => 12) 1 false [false, true] [true, false]
      (offDiagonalCoefficientRho datum scalars (fun _ => 12) 1 oddColour [false, true] [true, false] f) :=
  boundaryRho_offDiagonalLongSection datum scalars (fun _ => 12) 1 oddColour _ _ f

example (d : ℕ) (b : Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 0 false [false, true] [true, false]
      (offDiagonalCorrectedLift datum scalars (fun _ => 12) 0 oddColour [false, true] [true, false] d b) =
    (offDiagonalCoefficientRho datum scalars (fun _ => 12) 0 oddColour
      [false, true] [true, false])^[d] (Finsupp.single 0 b) :=
  offDiagonalLongExtraction_correctedLift datum scalars (fun _ => 12) 0 oddColour _ _ d b

/-- Empty old Homs retain the same unconditional operator comparison. -/
example (f : ℕ →₀ Old datum scalars (fun _ => 12) [] [true]) :
    boundaryRho datum scalars (fun _ => 12) oddColour [] [true, false]
      (offDiagonalLongSection datum scalars (fun _ => 12) 0 false [] [true] f) =
    offDiagonalLongSection datum scalars (fun _ => 12) 0 false [] [true]
      (offDiagonalCoefficientRho datum scalars (fun _ => 12) 0 oddColour [] [true] f) :=
  boundaryRho_offDiagonalLongSection datum scalars (fun _ => 12) 0 oddColour _ _ f

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRho
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

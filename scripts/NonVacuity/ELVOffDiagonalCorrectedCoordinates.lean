import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCorrectedCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

private def oddColour : {i : Bool // datum.parity i = 1} := ⟨false, rfl⟩

example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    (offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 1 oddColour
      [false, true] [true, false]).symm
      (offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 1 oddColour
        [false, true] [true, false] f) = f :=
  LinearEquiv.symm_apply_apply _ f

example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 0 oddColour
      [false, true] [true, false]
      ((offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 0 oddColour
        [false, true] [true, false]).symm f) = f :=
  LinearEquiv.apply_symm_apply _ f

/-- The basis change is compared with the actual corrected source lift at every degree. -/
example (d : ℕ) (b : Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 1 oddColour
      [false, true] [true, false] (Finsupp.single d b) =
    offDiagonalLongExtraction datum scalars (fun _ => 12) 1 false [false, true] [true, false]
      (offDiagonalCorrectedLift datum scalars (fun _ => 12) 1 oddColour
        [false, true] [true, false] d b) :=
  offDiagonalCorrectedCoordinateEquiv_single datum scalars (fun _ => 12) 1 oddColour _ _ d b

example (f : ℕ →₀ Old datum scalars (fun _ => 12) [] [true]) :
    (offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 0 oddColour [] [true]).symm
      (offDiagonalCorrectedCoordinateEquiv datum scalars (fun _ => 12) 0 oddColour [] [true] f) = f :=
  LinearEquiv.symm_apply_apply _ f

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCorrectedCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

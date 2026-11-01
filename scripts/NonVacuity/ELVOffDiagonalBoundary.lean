import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundary
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

example (z : Target datum scalars (fun _ => 12) false [false, true] ([true, false] ++ [false])) :
    appendC0 datum scalars (fun _ => 12) false [false, true] [true, false]
      (pMap datum scalars (fun _ => 12) false [false, true] ([true, false] ++ [false]) z) =
    offDiagonalPolynomialBoundary datum scalars (fun _ => 12) 1 false [false, true] [true, false]
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 1 false [false, true] [true, false] z) :=
  appendC0_pMap_offDiagonal datum scalars (fun _ => 12) 1 false [false, true] [true, false] z

example (z : Target datum scalars (fun _ => 12) true [] [false, true]) :
    appendC0 datum scalars (fun _ => 12) true [] [false]
      (pMap datum scalars (fun _ => 12) true [] [false, true] z) =
    offDiagonalPolynomialBoundary datum scalars (fun _ => 12) 0 true [] [false]
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 0 true [] [false] z) :=
  appendC0_pMap_offDiagonal datum scalars (fun _ => 12) 0 true [] [false] z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

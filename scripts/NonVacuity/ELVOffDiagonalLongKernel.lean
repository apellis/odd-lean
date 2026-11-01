import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongKernel
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

/-- The arbitrary-Hom kernel theorem is instantiated on reversed connected odd words. -/
example :
    LinearMap.ker
      (offDiagonalLongExtraction datum scalars (fun _ => 12) 1 false [false, true] [true, false]) =
      chronologicalShortSpan datum scalars (fun _ => 12) false [false, true] [true, false] :=
  ker_offDiagonalLongExtraction_eq_chronologicalShortSpan datum scalars (fun _ => 12)
    1 false [false, true] [true, false]

/-- The empty old Hom is included without supplying a normal-form index. -/
example :
    LinearMap.ker (offDiagonalLongExtraction datum scalars (fun _ => 12) 0 true [] [false]) =
      chronologicalShortSpan datum scalars (fun _ => 12) true [] [false] :=
  ker_offDiagonalLongExtraction_eq_chronologicalShortSpan datum scalars (fun _ => 12)
    0 true [] [false]

example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 0 true [false, true] [true, false]
      (offDiagonalLongSection datum scalars (fun _ => 12) 0 true [false, true] [true, false] f) = f :=
  offDiagonalLongExtraction_section datum scalars (fun _ => 12) 0 true _ _ f

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongKernel
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

private def crossingIndex : NFIdx [false, true] [true, false] :=
  ⟨([], Equiv.swap 0 1), by simp, by simp, by decide⟩

/-- A genuinely off-diagonal old Hom on connected odd data, with every
index and scalar hypothesis supplied. -/
example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    longHomExtraction datum scalars (fun _ => 12) 1 false crossingIndex
      (longHomSection datum scalars (fun _ => 12) 1 false crossingIndex f) = f :=
  longHomExtraction_section datum scalars (fun _ => 12) 1 false crossingIndex f

example : Function.Surjective
    (longHomExtraction datum scalars (fun _ => 12) 0 true crossingIndex) :=
  longHomExtraction_surjective datum scalars (fun _ => 12) 0 true crossingIndex

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

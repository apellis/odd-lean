import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightModulesExamples

private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private abbrev X := Bool → ℤ
private theorem step : (0 : X) + D.α false = D.α false := zero_add _

private def sourceVacuum : ELVWeightProduct D Sc (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D Sc (fun _ => 12) 12)
  else elvZeroModule D Sc (fun _ => 12) 12 β.1

example : PiSupercategory ℚ (ELVWeightProduct D Sc (fun _ => 12) 12 (0 : X) 0) :=
  elvWeightPi D Sc (fun _ => 12) 12 0 0

example : elvEFunctor D Sc (fun _ => 12) 12 false (0 : X) step ⊣
    (elvF D Sc (fun _ => 12) 12 false (0 : X) step).toFunctor :=
  elvWeightAdjunction D Sc (fun _ => 12) 12 false (0 : X) step

example :
    (elvEFunctor D Sc (fun _ => 12) 12 false (0 : X) step).map
      ((elvWeightAdjunction D Sc (fun _ => 12) 12 false (0 : X) step).unit.app sourceVacuum) ≫
      (elvWeightAdjunction D Sc (fun _ => 12) 12 false (0 : X) step).counit.app
        ((elvEFunctor D Sc (fun _ => 12) 12 false (0 : X) step).obj sourceVacuum) = 𝟙 _ :=
  (elvWeightAdjunction D Sc (fun _ => 12) 12 false (0 : X) step).left_triangle_components sourceVacuum

example :
    (elvWeightUnit D Sc (fun _ => 12) 12 false (0 : X) step).app sourceVacuum ∈
      parity (R := ℚ) _ _ 0 :=
  elvWeightUnit_mem D Sc (fun _ => 12) 12 false (0 : X) step sourceVacuum

end OddMath.QuiverHecke.ELVWeightModulesExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

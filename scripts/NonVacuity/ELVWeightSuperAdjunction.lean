import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightSuperAdjunctionExamples

private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private abbrev X := Bool → ℤ
private theorem step : (0 : X) + D.α false = D.α false := zero_add _

private def sourceVacuum : ELVWeightProduct D Sc (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D Sc (fun _ => 12) 12)
  else elvZeroModule D Sc (fun _ => 12) 12 β.1

example : SKM.SuperAdjunction (k := ℚ)
    (elvE D Sc (fun _ => 12) 12 false (0 : X) step)
    (elvF D Sc (fun _ => 12) 12 false (0 : X) step) :=
  elvActionAdjunction D Sc (fun _ => 12) 12 false (0 : X) step

example : (elvActionAdjunction D Sc (fun _ => 12) 12 false (0 : X) step).unit ∈
    parity (R := ℚ) _ _ 0 :=
  (elvActionAdjunction D Sc (fun _ => 12) 12 false (0 : X) step).unit_mem

example : (elvActionUnit D Sc (fun _ => 12) 12 false (0 : X) step).app 0 sourceVacuum =
    (elvWeightUnit D Sc (fun _ => 12) 12 false (0 : X) step).app sourceVacuum := rfl


example : SKM.SuperAdjunction (k := ℚ)
    (elvE D Sc (fun _ => 12) 12 false (0 : X) step)
    (elvF D Sc (fun _ => 12) 12 false (0 : X) step) :=
  ordinaryEvenSuperAdjunction
    (elvE D Sc (fun _ => 12) 12 false (0 : X) step)
    (elvF D Sc (fun _ => 12) 12 false (0 : X) step)
    (elvWeightAdjunction D Sc (fun _ => 12) 12 false (0 : X) step)
    (elvWeightUnit_mem D Sc (fun _ => 12) 12 false (0 : X) step)
    (elvWeightCounit_mem D Sc (fun _ => 12) 12 false (0 : X) step)


end OddMath.QuiverHecke.ELVWeightSuperAdjunctionExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

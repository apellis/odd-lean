import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightDotExamples

private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private abbrev X := Bool → ℤ
private theorem step : (0 : X) + D.α false = D.α false := zero_add _

private def sourceVacuum : ELVWeightProduct D Sc (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D Sc (fun _ => 12) 12)
  else elvZeroModule D Sc (fun _ => 12) 12 β.1

private def vacuumBlock : WeightBlocks D (0 : X) 0 :=
  ⟨0, by simp [blockWeight]⟩

example : elvActionDot D Sc (fun _ => 12) 12 false (0 : X) step ∈
    parity (R := ℚ) _ _ (D.parity false) :=
  elvActionDot_mem D Sc (fun _ => 12) 12 false (0 : X) step

example : HEq
    (elvContentDotTo D Sc (fun _ => 12) 12 false (0 : Multiset Bool)
      (0 + ([false] : Multiset Bool)) rfl)
    (contentInductionDot D Sc (fun _ => 12) 12 0 false) :=
  elvContentDotTo_heq D Sc (fun _ => 12) 12 false _ _ rfl

example :
    IsNilpotent (show End
      ((elvInductionComponent D Sc (fun _ => 12) 12 false (0 : X) step
        (blockSucc D 0 false step vacuumBlock)).obj sourceVacuum) from
      elvWeightDotComponent D Sc (fun _ => 12) 12 false (0 : X) step
        (D.parity false) sourceVacuum (blockSucc D 0 false step vacuumBlock)) :=
  elvWeightDotComponent_isNilpotent D Sc (fun _ => 12) 12 false (0 : X) step
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous
    sourceVacuum _


end OddMath.QuiverHecke.ELVWeightDotExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

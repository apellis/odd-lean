import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OddMath.QuiverHecke.ELVContentParityExamples

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev M := vacuumModule D Sc (fun _ => 12) 12
private abbrev V := vacuumObject D Sc (fun _ => 12) 12

example : supermoduleParityObj M ≅ M := supermoduleParityIso M

example : (supermoduleParityIso M).hom ≫ (supermoduleParityIso M).inv =
    𝟙 (supermoduleParityObj M) :=
  (supermoduleParityIso M).hom_inv_id

example : (supermoduleParityIso M).inv ≫ (supermoduleParityIso M).hom = 𝟙 M :=
  (supermoduleParityIso M).inv_hom_id

example : (supermoduleParityIso M).hom ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem M

example : (supermoduleParityIso M).hom.app 1 V =
    (PiSupercategory.ζ (R := ℚ) (M.obj V)).hom := rfl

example : PiSupercategory ℚ (ContentModules D Sc (fun _ => 12) 12 0) :=
  contentModulesPi D Sc (fun _ => 12) 12 0

end OddMath.QuiverHecke.ELVContentParityExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

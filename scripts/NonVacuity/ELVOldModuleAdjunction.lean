import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
namespace OldModuleAdjunctionConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private abbrev M := oldRepresentable D Sc cutoff (⟨[false, true]⟩ : OldCategory D Sc cutoff)
example (r : ZMod 2) :    (oldModuleMate D Sc cutoff false).app r M =
      (BalancedInduction.adjunctionUnit (append D Sc cutoff false)).app
        ((BalancedInduction.induction (append D Sc cutoff false)).obj
          ((BalancedInduction.restriction (append D Sc cutoff false)).obj M)) ≫
        (BalancedInduction.restriction (append D Sc cutoff false)).map
          ((signedEqualInductionCross D Sc cutoff false).app r
            ((BalancedInduction.restriction (append D Sc cutoff false)).obj M)) ≫
        (BalancedInduction.restriction (append D Sc cutoff false)).map
          ((BalancedInduction.induction (append D Sc cutoff false)).map
            ((BalancedInduction.adjunctionCounit (append D Sc cutoff false)).app M)) := by
  exact oldModuleMate_app D Sc cutoff false r M
example : (oldAppendAdjunction D Sc cutoff false).counit.app 1 M = 0 := by
  simp only [oldAppendAdjunction_counit_app, one_ne_zero, ↓reduceIte]
end OldModuleAdjunctionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"

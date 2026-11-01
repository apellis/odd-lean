import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapInput
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
namespace ActualCapInputConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private def j : {j : Bool // D.parity j = 1} := ⟨false, rfl⟩
example (g : Old D Sc cutoff ([false, true] ++ [false]) [true, false, false])
    (b : Old D Sc cutoff [false, true, false] ([false, true] ++ [false])) :
    actualShiftedInputContraction D Sc cutoff false [false, true, false] [true, false, false]
      (BalancedInduction.tensor (append D Sc cutoff false)
        (coefficientOneModule D Sc cutoff false [false, true, false]).toFunctor
        (⟨[false, true]⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff [false, true, false] ([false, true] ++ [false])
        [true, false, false]
        (oldTwist D Sc cutoff 1 [false, true, false] ([false, true] ++ [false]) b) g :=
  actualShiftedInputContraction_tensor D Sc cutoff false _ _ _ g b
example (v t : List Bool) (z : actualShiftedSourceSpace D Sc cutoff j.1 v t) :
    actualSourceInputDot D Sc cutoff j v t (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t (actualShiftedInputDot D Sc cutoff j v t z) :=
  actualSourceInputDot_carrier D Sc cutoff j v t z
end ActualCapInputConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVActualCapInput
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"

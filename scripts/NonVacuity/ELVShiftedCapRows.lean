import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCapRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
namespace ShiftedCapRowsConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private def j : {j : Bool // D.parity j = 1} := ⟨false, rfl⟩
example (v t : List Bool) (n : ℕ)
    (z : (actualUnshiftedSourceModule D Sc cutoff false v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capRowSign (k := ℚ) n • oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t
      (actualShiftedInputContraction D Sc cutoff false v t
        ((actualShiftedInputDot D Sc cutoff j v t)^[n]
          ((shiftedSourceParityIso D Sc cutoff false v).hom.total
            (⟨t⟩ : OldCategory D Sc cutoff) z))) =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff false)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((actualInductionDot D Sc cutoff false
            ((BalancedInduction.restriction (append D Sc cutoff false)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) :=
  shiftedCapRow_normalization D Sc cutoff j v t n z
end ShiftedCapRowsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCapRows
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"


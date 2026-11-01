import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapParity
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
namespace ActualCapParityConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private def j : {j : Bool // D.parity j = 1} := ⟨false, rfl⟩
example (v : List Bool) :
    (shiftedSourceParityIso D Sc cutoff false v).hom ∈ parity (R := ℚ) _ _ 1 :=
  shiftedSourceParityIso_hom_mem D Sc cutoff false v
example (v : List Bool) :
    shiftedSourceCounit D Sc cutoff false v ∈ parity (R := ℚ) _ _ 1 :=
  shiftedSourceCounit_mem D Sc cutoff false v
example (v t : List Bool)
    (z : (actualUnshiftedSourceModule D Sc cutoff false v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    actualInductionDot D Sc cutoff false (coefficientOneModule D Sc cutoff false v)
      (⟨t⟩ : OldCategory D Sc cutoff)
      ((shiftedSourceParityIso D Sc cutoff false v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
      -(shiftedSourceParityIso D Sc cutoff false v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (actualInductionDot D Sc cutoff false
          ((BalancedInduction.restriction (append D Sc cutoff false)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
          (⟨t⟩ : OldCategory D Sc cutoff) z) :=
  actualInductionDot_sourceParity D Sc cutoff j v t z
end ActualCapParityConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVActualCapParity
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"


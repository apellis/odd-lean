import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace ShiftedCoefficientModuleConsumer
open OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom ≫ shiftedSourceCounit D Sc cutoff i v =
      (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) :=
  shiftedSourceParityIso_counit D Sc cutoff i v

def literalSource (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      (coefficientOneModule D Sc cutoff j.1 v)).obj (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t :=
  coefficientOneSourceEquiv D Sc cutoff j v t

end ShiftedCoefficientModuleConsumer

namespace MovingCoefficientConcreteConsumer
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private abbrev j : {i : Bool // D.parity i = 1} := ⟨false, rfl⟩
example : movingCoefficientModule D Sc cutoff j [true, false] ≅
    coefficientOneModule D Sc cutoff false [true, false] :=
  movingCoefficientIso D Sc cutoff j [true, false]
example : Function.Bijective
    (coefficientOneSourceEquiv D Sc cutoff j [true, false] [true, false]) :=
  (coefficientOneSourceEquiv D Sc cutoff j [true, false] [true, false]).bijective
end MovingCoefficientConcreteConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientModule
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"

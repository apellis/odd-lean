import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientComparison
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace ShiftedCoefficientComparisonConsumer
open OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) (v : List I) (s : OldCategory D Sc cutoff) (q : ZMod 2) :
    ((coefficient D Sc cutoff 1 i v).obj s).proj q =
      ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj q :=
  coefficientOne_obj_proj D Sc cutoff i v s q
example (i : I) (v : List I) (s : OldCategory D Sc cutoff) :
    (coefficientParityIso D Sc cutoff i v).hom.app s ∈
      parity (R := k) ((coefficient D Sc cutoff 1 i v).obj s)
        ((parityRestrictedRepresentable D Sc cutoff i v).obj s) 0 :=
  coefficientParityIso_hom_mem D Sc cutoff i v s
end ShiftedCoefficientComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"

import OddMath.QuiverHecke.CyclotomicAction.ELVCapInputRecurrence
import Lean.Util.CollectAxioms
noncomputable section
namespace CapInputRecurrenceConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)

example (f : ℕ →₀ Old D Sc cutoff v v) :
    inputContractionAffine D Sc cutoff j v (boundaryCrossCoordinates D Sc cutoff p j v f) =
      outputPolynomialBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) 0 :=
  inputContractionAffine_boundaryCrossCoordinates D Sc cutoff p j v f

example (r d : ℕ) (b : Old D Sc cutoff v v)
    (h : outputSDegree D j.1 v = r + d + 1 + endpointQPDegree D cutoff j.1 v) :
    inputContraction D Sc cutoff j v
      ((crossingInputDot D Sc cutoff j v)^[r]
        (q D Sc cutoff j.1 v v
          (boundaryCrossCoordinates D Sc cutoff p j v
            (outputLongExtraction D Sc cutoff p j.1 v
              (outputCorrectedLift D Sc cutoff p j v d b))))) =
      outputBoundaryLeadingEquiv D Sc cutoff p j v 0 b := by
  rw [inputContraction_iterate_q]
  exact inputContractionAffine_corrected_pivot D Sc cutoff p j v r d b h
end CapInputRecurrenceConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCapInputRecurrence
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"

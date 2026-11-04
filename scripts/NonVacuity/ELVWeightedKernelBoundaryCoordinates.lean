import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedKernelBoundaryCoordinates
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedKernelBoundaryCoordinateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private theorem positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (s.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool)
    (j : Fin (CyclotomicCrossingTensor.contentUnitCount D cut i (s.word : Multiset Bool))) (r : ℕ) :=
  weightedContentUnitBoundaryValue_atWord D Sc cut 8 i M s (positive i) j r (𝟙 (Q.obj s))
example (i : Bool)
    (j : Fin (CyclotomicCrossingTensor.contentUnitCount D cut i (s.word : Multiset Bool))) (r : ℕ) :=
  weightedContentUnitBoundaryValue_coefficient D Sc cut 8 i M s (positive i) j r (𝟙 (Q.obj s))
example (i : Bool)
    (j : Fin (CyclotomicCrossingTensor.contentUnitCount D cut i (s.word : Multiset Bool))) (r : ℕ) :=
  weightedUnitBoundaryCoefficient_degree D Sc cut 8 i sy hc s (positive i) j r
example : CyclotomicCrossingTensor.contentUnitCount D cut false (s.word : Multiset Bool) = 8 := by decide
example : CyclotomicCrossingTensor.contentUnitCount D cut true (s.word : Multiset Bool) = 10 := by decide

private abbrev cutOne : Bool → ℕ := fun _ => 1
private abbrev Qone := oldTruncateFunctor D Sc cutOne 4
private abbrev oneWord (i : Bool) : OldCategory D Sc cutOne := ⟨[i]⟩
private def oneModule (i : Bool) : Superfunctor ℚ (TruncatedCategory D Sc cutOne 4) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cutOne 4 (Qone.obj (oneWord i))
private theorem negative (i : Bool) :
    CyclotomicCrossingTensor.contentCrossingHeight D cutOne i ((oneWord i).word : Multiset Bool) ≤ 0 := by
  cases i <;> decide
example (i : Bool)
    (j : Fin (CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool))) (r : ℕ) :=
  weightedContentCapBoundaryValue_atWord D Sc cutOne 4 i (oneModule i)
    (oneWord i) (negative i) r j (𝟙 (Qone.obj (oneWord i)))
example (i : Bool)
    (j : Fin (CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool))) (r : ℕ) :=
  weightedContentCapBoundaryValue_coefficient D Sc cutOne 4 i (oneModule i)
    (oneWord i) (negative i) r j (𝟙 (Qone.obj (oneWord i)))
example (i : Bool)
    (j : Fin (CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool))) (r : ℕ) :=
  weightedCapBoundaryCoefficient_degree D Sc cutOne 4 i sy hc (oneWord i) (negative i) r j
example (i : Bool) : CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool) = 1 := by
  cases i <;> decide
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end WeightedKernelBoundaryCoordinateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedKernelBoundaryCoordinates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

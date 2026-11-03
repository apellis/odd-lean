import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentMatrixInverse
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedContentMatrixConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]
private theorem hDot (i : Bool) : IsSupernatural ℚ (D.parity i)
    (truncatedAppendComponent D Sc cut 8 (dotE D Sc [i] 0)) :=
  truncatedAppendComponent_supernatural D Sc cut 8 (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

private theorem positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (s.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := weightedContentUnitMatrixMap_bijective D Sc cut 8 i M (s.word : Multiset Bool) (positive i) ⟨Q.obj s, rfl⟩
example (i : Bool) := weightedContentUnitMatrixIso D Sc cut 8 i M (s.word : Multiset Bool) (positive i)
example (i : Bool) := weightedContentUnitMatrixIso_hom D Sc cut 8 i M (s.word : Multiset Bool) (positive i)
example (i : Bool) := weightedContentUnitMatrixMap_mem D Sc cut 8 i M (s.word : Multiset Bool)
example (i : Bool) := weightedContentUnitMatrixIso_inv_mem D Sc cut 8 i M (s.word : Multiset Bool) (positive i)
example (i : Bool) := weightedContentUnitMatrix_hom_inv_id D Sc cut 8 i M (s.word : Multiset Bool) (positive i)
example (i : Bool) := weightedContentUnitMatrix_inv_hom_id D Sc cut 8 i M (s.word : Multiset Bool) (positive i)
example (i : Bool) := weightedContentUnitMatrixIso_hom_total D Sc cut 8 i M
  (s.word : Multiset Bool) (positive i) ⟨Q.obj s, rfl⟩
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
example (i : Bool) := weightedContentCapMatrixMap_bijective D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool) (negative i) ⟨Qone.obj (oneWord i), rfl⟩
example (i : Bool) := weightedContentCapMatrixIso D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool) (negative i)
example (i : Bool) := weightedContentCapMatrixIso_hom D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool) (negative i)
example (i : Bool) := weightedContentCapMatrixMap_mem D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool)
example (i : Bool) := weightedContentCapMatrixIso_inv_mem D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool) (negative i)
example (i : Bool) := weightedContentCapMatrix_hom_inv_id D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool) (negative i)
example (i : Bool) := weightedContentCapMatrix_inv_hom_id D Sc cutOne 4 i (oneModule i) ((oneWord i).word : Multiset Bool) (negative i)
example (i : Bool) := weightedContentCapMatrixIso_hom_total D Sc cutOne 4 i (oneModule i)
  ((oneWord i).word : Multiset Bool) (negative i) ⟨Qone.obj (oneWord i), rfl⟩
example (i : Bool) : CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool) = 1 := by
  cases i <;> decide

private abbrev cutTwo : Bool → ℕ := fun _ => 2
private abbrev Qtwo := oldTruncateFunctor D Sc cutTwo 4
private abbrev zeroWord (i : Bool) : OldCategory D Sc cutTwo := ⟨[i]⟩
private def zeroModule (i : Bool) : Superfunctor ℚ (TruncatedCategory D Sc cutTwo 4) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cutTwo 4 (Qtwo.obj (zeroWord i))
private theorem zero_positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cutTwo i ((zeroWord i).word : Multiset Bool) := by
  cases i <;> decide
private theorem zero_negative (i : Bool) :
    CyclotomicCrossingTensor.contentCrossingHeight D cutTwo i ((zeroWord i).word : Multiset Bool) ≤ 0 := by
  cases i <;> decide
example (i : Bool) := weightedContentUnitMatrixIso_hom D Sc cutTwo 4 i (zeroModule i) ((zeroWord i).word : Multiset Bool) (zero_positive i)
example (i : Bool) := weightedContentCapMatrixIso_hom D Sc cutTwo 4 i (zeroModule i) ((zeroWord i).word : Multiset Bool) (zero_negative i)
example (i : Bool) : CyclotomicCrossingTensor.contentUnitCount D cutTwo i ((zeroWord i).word : Multiset Bool) = 0 := by
  cases i <;> decide
example (i : Bool) : CyclotomicCrossingTensor.contentCapCount D cutTwo i ((zeroWord i).word : Multiset Bool) = 0 := by
  cases i <;> decide

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
private theorem vacuum_positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (vacuum.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := weightedContentUnitMatrixIso_hom D Sc cut 8 i vacuumModule (vacuum.word : Multiset Bool) (vacuum_positive i)
example (i : Bool) := weightedContentUnitMatrix_inv_hom_id D Sc cut 8 i vacuumModule (vacuum.word : Multiset Bool) (vacuum_positive i)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end WeightedContentMatrixConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentMatrixInverse
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

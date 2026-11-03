import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedFiniteMatrixComparison
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedFiniteMatrixConsumer
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

example (i : Bool) (m : ℕ) (w : OldCategory D Sc cut) := weightedMatrixCharts_unitMatrix D Sc cut 8 i M m w
example (i : Bool) (m : ℕ) (w : OldCategory D Sc cut) := weightedMatrixCharts_capMatrix D Sc cut 8 i M m w
example (i : Bool) := weightedMatrixCharts_unitMatrix D Sc cut 8 i M
  (CyclotomicCrossingTensor.contentUnitCount D cut i (s.word : Multiset Bool)) s
example : CyclotomicCrossingTensor.contentUnitCount D cut false (s.word : Multiset Bool) = 8 := by decide
example : CyclotomicCrossingTensor.contentUnitCount D cut true (s.word : Multiset Bool) = 10 := by decide
private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) (m : ℕ) := weightedMatrixCharts_unitMatrix D Sc cut 8 i vacuumModule m vacuum
example (i : Bool) (m : ℕ) := weightedMatrixCharts_capMatrix D Sc cut 8 i vacuumModule m vacuum
private abbrev cutOne : Bool → ℕ := fun _ => 1
private abbrev Qone := oldTruncateFunctor D Sc cutOne 4
private abbrev oneWord (i : Bool) : OldCategory D Sc cutOne := ⟨[i]⟩
private def oneModule (i : Bool) : Superfunctor ℚ (TruncatedCategory D Sc cutOne 4) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cutOne 4 (Qone.obj (oneWord i))
example (i : Bool) := weightedMatrixCharts_capMatrix D Sc cutOne 4 i (oneModule i) 1 (oneWord i)
example (i : Bool) : CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool) = 1 := by
  cases i <;> decide
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end WeightedFiniteMatrixConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedFiniteMatrixComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

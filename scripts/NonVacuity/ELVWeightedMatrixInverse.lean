import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixInverse
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedMatrixInverseConsumer
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

example (i : Bool) (m : ℕ) (a : Option (Fin m)) (w : OldCategory D Sc cut) :=
  weightedUnitFamilyValueEquiv D Sc cut 8 i M m w a
example (i : Bool) (m : ℕ) (a : Option (Fin m)) (w : OldCategory D Sc cut) :=
  weightedCapFamilyValueEquiv D Sc cut 8 i M m w a
example (i : Bool) (m : ℕ) (w : OldCategory D Sc cut) := weightedUnitMatrixValueEquiv D Sc cut 8 i M m w
example (i : Bool) (m : ℕ) (w : OldCategory D Sc cut) := weightedCapMatrixValueEquiv D Sc cut 8 i M m w
example (i : Bool) (n : ℕ) (w : OldCategory D Sc cut) (b : (weightedRestriction D Sc cut 8 M).obj w) :=
  weightedUnitColumnValue_compare D Sc cut 8 i M w n b
example (i : Bool) (n : ℕ) (w : OldCategory D Sc cut)
    (x : ((BalancedInduction.induction (J i)).obj
      ((BalancedInduction.restriction (J i)).obj (weightedRestriction D Sc cut 8 M))).obj w) :=
  weightedCapRowValue_compare D Sc cut 8 i M w n x
example (i : Bool) (w : OldCategory D Sc cut)
    (x : ((BalancedInduction.induction (J i)).obj
      ((BalancedInduction.restriction (J i)).obj (weightedRestriction D Sc cut 8 M))).obj w) :=
  weightedMateValue_compare D Sc cut 8 i M w x

example (i : Bool) (w : OldCategory D Sc cut)
    (x : ((BalancedInduction.induction (J i)).obj
      ((BalancedInduction.restriction (J i)).obj (weightedRestriction D Sc cut 8 M))).obj w) :=
  weightedMateTotalValue_compare D Sc cut 8 i M w x

private theorem mixed_height (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (s.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := weightedModuleUnitMatrixIso D Sc cut 8 i M s (mixed_height i)
example (i : Bool) := (weightedModuleUnitMatrixIso D Sc cut 8 i M s (mixed_height i)).hom_inv_id
example (i : Bool) := (weightedModuleUnitMatrixIso D Sc cut 8 i M s (mixed_height i)).inv_hom_id

private abbrev cutOne : Bool → ℕ := fun _ => 1
private abbrev Qone := oldTruncateFunctor D Sc cutOne 4
private abbrev oneWord (i : Bool) : OldCategory D Sc cutOne := ⟨[i]⟩
private def oneModule (i : Bool) : Superfunctor ℚ (TruncatedCategory D Sc cutOne 4) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cutOne 4 (Qone.obj (oneWord i))
private theorem one_height (i : Bool) :
    CyclotomicCrossingTensor.contentCrossingHeight D cutOne i ((oneWord i).word : Multiset Bool) ≤ 0 := by
  cases i <;> decide
example (i : Bool) := weightedModuleCapMatrixIso D Sc cutOne 4 i (oneModule i) (oneWord i) (one_height i)
example (i : Bool) := (weightedModuleCapMatrixIso D Sc cutOne 4 i (oneModule i) (oneWord i) (one_height i)).hom_inv_id
example (i : Bool) := (weightedModuleCapMatrixIso D Sc cutOne 4 i (oneModule i) (oneWord i) (one_height i)).inv_hom_id

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
private theorem vacuum_height (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (vacuum.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := weightedModuleUnitMatrixIso D Sc cut 8 i vacuumModule vacuum (vacuum_height i)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end WeightedMatrixInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixInverse
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

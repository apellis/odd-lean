import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedMatrixComponentsConsumer
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

example (i : Bool) := weightedMatrixMate_mem D Sc cut 8 i M
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  weightedUnitMatrixEntry_mem D Sc cut 8 i M m a
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  weightedCapMatrixEntry_mem D Sc cut 8 i M m a
example (i : Bool) (m : ℕ) (w : TruncatedCategory D Sc cut 8) :=
  weightedUnitMatrixComponent_even D Sc cut 8 i M m w
example (i : Bool) (m : ℕ) (w : TruncatedCategory D Sc cut 8) :=
  weightedCapMatrixComponent_even D Sc cut 8 i M m w
example (i : Bool) (w : TruncatedCategory D Sc cut 8)
    (x : BalancedInduction.Obj (T i) ((BalancedInduction.restriction (T i)).obj M).toFunctor w) :=
  BalancedInduction.inductionMatrixMate_apply (T i)
    (truncatedEqualCross_supernatural D Sc cut 8 i) (truncatedDot_supernatural D Sc cut 8 i)
    (by cases i <;> decide) M w x
example (i : Bool) (m : ℕ) := weightedUnitMatrixEntry_none D Sc cut 8 i M m
example (i : Bool) (m : ℕ) (r : Fin m) := weightedUnitMatrixEntry_some D Sc cut 8 i M m r
example (i : Bool) (m : ℕ) := weightedCapMatrixEntry_none D Sc cut 8 i M m
example (i : Bool) (m : ℕ) (r : Fin m) := weightedCapMatrixEntry_some D Sc cut 8 i M m r
example (i : Bool) (w : OldCategory D Sc cut)
    (x : ((BalancedInduction.induction (J i)).obj
      ((BalancedInduction.restriction (J i)).obj (weightedRestriction D Sc cut 8 M))).obj w) :=
  weightedMatrixMateValue_eq_total D Sc cut 8 i M (Q.obj w)
    (weightedMateSourceLinearEquiv D Sc cut 8 i M w x)
example (i : Bool) (w : OldCategory D Sc cut)
    (x : ((BalancedInduction.induction (J i)).obj
      ((BalancedInduction.restriction (J i)).obj (weightedRestriction D Sc cut 8 M))).obj w) :=
  BalancedInduction.inductionMatrixMate_value_apply (T i)
    (truncatedEqualCross_supernatural D Sc cut 8 i) (truncatedDot_supernatural D Sc cut 8 i)
    (by cases i <;> decide) M (Q.obj w) (weightedMateSourceLinearEquiv D Sc cut 8 i M w x)
example (i : Bool) (m : ℕ) (w : TruncatedCategory D Sc cut 8) :=
  BalancedInduction.inductionUnitMatrixEntry_none_total (T i)
    (truncatedEqualCross_supernatural D Sc cut 8 i) (truncatedDot_supernatural D Sc cut 8 i)
    (by cases i <;> decide) M m w
example (i : Bool) (m : ℕ) (r : Fin m) (w : TruncatedCategory D Sc cut 8) :=
  BalancedInduction.inductionUnitMatrixEntry_some_total (T i)
    (truncatedEqualCross_supernatural D Sc cut 8 i) (truncatedDot_supernatural D Sc cut 8 i)
    (by cases i <;> decide) M m r w
example (i : Bool) (m : ℕ) (w : TruncatedCategory D Sc cut 8) :=
  BalancedInduction.inductionCapMatrixEntry_none_total (T i)
    (truncatedEqualCross_supernatural D Sc cut 8 i) (truncatedDot_supernatural D Sc cut 8 i)
    (by cases i <;> decide) M m w
example (i : Bool) (m : ℕ) (r : Fin m) (w : TruncatedCategory D Sc cut 8) :=
  BalancedInduction.inductionCapMatrixEntry_some_total (T i)
    (truncatedEqualCross_supernatural D Sc cut 8 i) (truncatedDot_supernatural D Sc cut 8 i)
    (by cases i <;> decide) M m r w
/-- Both moving colours are present in the concrete datum. -/
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) (m : ℕ) :=
  weightedUnitMatrixComponent_even D Sc cut 8 i vacuumModule m (Q.obj vacuum)
example (i : Bool) (m : ℕ) :=
  weightedCapMatrixComponent_even D Sc cut 8 i vacuumModule m (Q.obj vacuum)
end WeightedMatrixComponentsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

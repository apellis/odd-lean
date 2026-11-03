import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedMatrixRowsConsumer
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

example (i : Bool) (n : ℕ) := BalancedInduction.unitDotColumn_mem (T i) (hDot i) M n
example (i : Bool) (n : ℕ) := BalancedInduction.capDotRow_mem (T i) (hDot i) M n
example (i : Bool) (n : ℕ) (w : TruncatedCategory D Sc cut 8) :=
  BalancedInduction.unitDotColumn_total (T i) (hDot i) M n w
example (i : Bool) (n : ℕ) (w : TruncatedCategory D Sc cut 8) :=
  BalancedInduction.capDotRow_total (T i) (hDot i) M n w
/-- All powers of the actual unscaled prescribed rows use the exact charts. -/
example (i : Bool) (n : ℕ) (w : OldCategory D Sc cut) :=
  weightedMateTargetLinear_unitDot D Sc cut 8 i M w n
example (i : Bool) (n : ℕ) (w : OldCategory D Sc cut) :=
  weightedMateSourceLinear_capDot D Sc cut 8 i M w n
example (i : Bool) (w : OldCategory D Sc cut) := weightedMateSourceLinear_counit D Sc cut 8 i M w
example (i : Bool) (n : ℕ) := oldUnitColumn_eq D Sc cut i (weightedRestriction D Sc cut 8 M) n
example (i : Bool) (n : ℕ) := oldCapRow_eq D Sc cut i (weightedRestriction D Sc cut 8 M) n
example (i : Bool) := truncatedModuleDot_eq D Sc cut 8 i M

/-- The odd crossing has odd parity, and its extra sign remains explicit. -/
example : D.parity true * D.parity true = 1 := by decide
example : D.parity false * D.parity false = 0 := by decide
example : (sign ℚ (D.parity true * D.parity true) : ℚ) = -1 := by decide

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) (n : ℕ) :=
  BalancedInduction.unitDotColumn_total (T i) (hDot i) vacuumModule n (Q.obj vacuum)
example (i : Bool) (n : ℕ) := weightedMateTargetLinear_unitDot D Sc cut 8 i vacuumModule vacuum n
example (i : Bool) (n : ℕ) := weightedMateSourceLinear_capDot D Sc cut 8 i vacuumModule vacuum n
end WeightedMatrixRowsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMatrixNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace MatrixNaturalityConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]
private abbrev hDot (i : Bool) := truncatedDot_supernatural D Sc cut 8 i
private abbrev hCross (i : Bool) := truncatedEqualCross_supernatural D Sc cut 8 i
private abbrev odd := supermoduleParityIso_hom_mem M
local instance : PiSupercategory ℚ (Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ)) :=
  supermodulePiSupercategory

example (i : Bool) (n : ℕ) := dotEnd_power_supernatural (T i) (hDot i) n
example (i : Bool) (n : ℕ) := (unitDotColumn_supernatural (T i) (hDot i) n).naturality odd
example (i : Bool) (n : ℕ) := (capDotRow_supernatural (T i) (hDot i) n).naturality odd
example (i : Bool) := (orderedMateComponent_supernatural (T i) (hCross i)).naturality odd
example (i : Bool) (n : ℕ) {L P : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ)} (f : L ⟶ P) :=
  (SKM.IsSupernatural.shiftSource (unitDotColumn_supernatural (T i) (hDot i) n)).toNatTrans.naturality f
example (i : Bool) (n : ℕ) {L P : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ)} (f : L ⟶ P) :=
  (SKM.IsSupernatural.shiftTarget (capDotRow_supernatural (T i) (hDot i) n)).toNatTrans.naturality f
example (i : Bool) {L P : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ)} (f : L ⟶ P) :=
  (SKM.IsSupernatural.shiftSource (orderedMateComponent_supernatural (T i) (hCross i))).toNatTrans.naturality f
private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def V : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) (n : ℕ) := (unitDotColumn_supernatural (T i) (hDot i) n).naturality (supermoduleParityIso_hom_mem V)
example (i : Bool) := (orderedMateComponent_supernatural (T i) (hCross i)).naturality (supermoduleParityIso_hom_mem V)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end MatrixNaturalityConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionMatrixNaturality
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction BalancedInduction
namespace WeightedMateIdentificationConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def M (v : List Bool) := supermoduleParityObj
  (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
    ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩))
/-- Both degrees and inhomogeneous coefficient words retain the whole selected mate. -/
example (i : Bool) := weightedMatrixMate_eq_ordered D Sc cut 8 i (M [i,!i])
example (i : Bool) := inductionMatrixMate_eq
  (truncatedAppend D Sc cut 8 [i]) (truncatedEqualCross_supernatural D Sc cut 8 i)
  (truncatedDot_supernatural D Sc cut 8 i) (SKM.zmod2_mul_self (D.parity i)) (M [!i,i])
/-- The vacuum representable is included without imposing a nonzero height premise. -/
example (i : Bool) := weightedMatrixMate_eq_ordered D Sc cut 8 i (M [])
end WeightedMateIdentificationConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

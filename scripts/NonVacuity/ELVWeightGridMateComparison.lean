import OddMath.QuiverHecke.CyclotomicAction.ELVWeightGridMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightGridMateComparisonConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem lower (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem upper (i : Bool) : D.α i + D.α i = D.α i + D.α i := rfl
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
private def lowerBlock : WeightBlocks D 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
/-- The whole selected principal field is compared for even and odd colours. -/
example (i : Bool) := elvWeightRouquierGridMate_comparison D Sc cut 8 i 0
  (lower i) (upper i) lowerBlock (M i)
/-- Empty truncation retains the selected cup-crossing-cap comparison. -/
private def emptyM (i : Bool) : ELVWeightProduct D Sc (fun _ => 0) 0 0 (D.α i) := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc (fun _ => 0) 0 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (fun _ => 0) 0
      ((oldTruncateFunctor D Sc (fun _ => 0) 0).obj ⟨[i]⟩))
example (i : Bool) := elvWeightRouquierGridMate_comparison D Sc (fun _ => 0) 0 i 0
  (lower i) (upper i) lowerBlock (emptyM i)
end WeightGridMateComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightGridMateComparison
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightMixedMateComparisonConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private def family (x : Bool → ℤ) (v : List Bool) : ELVWeightProduct D Sc cut 8 0 x := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))

private def lowerBlock : WeightBlocks D 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
private theorem h₁ (i : Bool) : (0 : Bool → ℤ) + D.α (!i) = D.α (!i) := zero_add _
private theorem h₂ (i : Bool) : D.α (!i) + D.α i = D.α (!i) + D.α i := rfl
private theorem h₃ (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem h₄ (i : Bool) : D.α i + D.α (!i) = D.α (!i) + D.α i := add_comm _ _

/-- The selected upper cup preserves both supported mixed coordinates. -/
example (i : Bool) := elvWeightMixedUnit_comparison D Sc cut 8 i (!i) 0
  (h₁ i) (h₃ i) (h₄ i) lowerBlock (family (D.α (!i)) [!i])
example (i : Bool) := elvInductionComponent_map_of D Sc cut 8 (!i) 0 (h₁ i)
  lowerBlock (blockSucc D 0 (!i) (h₁ i) lowerBlock) rfl (𝟙 (family 0 []))
/-- The lower cap uses the same supported upper block and actual input component. -/
example (i : Bool) := elvWeightMixedCounit_comparison D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) lowerBlock (family (D.α (!i)) [!i])
end WeightMixedMateComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateComparison
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightAbsentUnitInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private theorem cutoff (i : Bool) : (cut i : ℤ) = D.h i Λ := rfl
private theorem lower (x : Bool → ℤ) (i : Bool) : (x - D.α i) + D.α i = x := sub_add_cancel _ _
private def family (x : Bool → ℤ) (v : List Bool) : ELVWeightProduct D Sc cut 8 Λ x := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))
private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private def otherBlock (i : Bool) : WeightBlocks D Λ (D.α (!i) - Λ) := ⟨{!i}, by simp⟩
private theorem emptyAbsent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (lower (-Λ) i) β = emptyBlock := by
  intro h
  have hi := (exists_blockSucc_iff D Λ i (lower (-Λ) i) emptyBlock).mp h
  simp [emptyBlock] at hi
private theorem otherAbsent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (lower (D.α (!i) - Λ) i) β = otherBlock i := by
  intro h
  have hi := (exists_blockSucc_iff D Λ i (lower (D.α (!i) - Λ) i) (otherBlock i)).mp h
  cases i <;> simp [otherBlock] at hi
private theorem emptyHasInverse (i : Bool) :=
  (elvWeightAbsentUnitInverse_nonempty D Sc cut 8 i Λ (lower (-Λ) i) rfl emptyBlock
    (cutoff i) (emptyAbsent i) (family (-Λ) []))
private theorem otherHasInverse (i : Bool) :=
  (elvWeightAbsentUnitInverse_nonempty D Sc cut 8 i Λ (lower (D.α (!i) - Λ) i) rfl (otherBlock i)
    (cutoff i) (otherAbsent i) (family (D.α (!i) - Λ) [!i]))
/-- Both moving parities retain actual native mate/unit-power fields on absent blocks. -/
example (i : Bool) := (Classical.choice (emptyHasInverse i)).total
example (i : Bool) := (Classical.choice (emptyHasInverse i)).ff
example (i : Bool) := (Classical.choice (emptyHasInverse i)).f'_mem
example (i : Bool) (n : ℕ) := (Classical.choice (emptyHasInverse i)).g'_mem n
example (i : Bool) := (Classical.choice (otherHasInverse i)).total
example (i : Bool) := (Classical.choice (otherHasInverse i)).ff
example (i : Bool) := (Classical.choice (otherHasInverse i)).f'_mem
example (i : Bool) (n : ℕ) := (Classical.choice (otherHasInverse i)).g'_mem n
example (i : Bool) := (Classical.choice (emptyHasInverse i)).fg 0 (by cases i <;> decide)
example (i : Bool) := (Classical.choice (emptyHasInverse i)).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (Classical.choice (otherHasInverse i)).gf 0 (by cases i <;> decide)
example (i : Bool) := (Classical.choice (otherHasInverse i)).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
end WeightAbsentUnitInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentUnitInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

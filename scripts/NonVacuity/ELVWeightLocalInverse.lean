import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightLocalInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem cutoff (i : Bool) : (cut i : ℤ) = D.h i Λ := rfl
private def M (v : List Bool) (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (w v + D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v ++ [i]⟩)))
private theorem negative (i : Bool) : D.h i (w [] + D.α i) ≤ 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem positive (i : Bool) : 0 ≤ D.h i (w [i,i] + D.α i) := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem middle (i : Bool) : D.h i (w [i] + D.α i) = 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
example (i : Bool) := (Classical.choice (elvWeightLocalUnitInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [] i) (cutoff i) (negative i))).total
example (i : Bool) := (Classical.choice (elvWeightLocalUnitInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [] i) (cutoff i) (negative i))).ff
example (i : Bool) (n : ℕ) := (Classical.choice (elvWeightLocalUnitInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [] i) (cutoff i) (negative i))).g'_mem n
example (i : Bool) := (Classical.choice (elvWeightLocalUnitInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [] i) (cutoff i) (negative i))).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (Classical.choice (elvWeightLocalUnitFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (negative i))).total
example (i : Bool) := (Classical.choice (elvWeightLocalUnitFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (negative i))).ff
example (i : Bool) := (Classical.choice (elvWeightLocalUnitFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (negative i))).f'_mem
example (i : Bool) (n : ℕ) := (Classical.choice (elvWeightLocalUnitFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (negative i))).g'_mem n
example (i : Bool) := (Classical.choice (elvWeightLocalUnitFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (negative i))).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (Classical.choice (elvWeightLocalCapInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [i,i] i) (cutoff i) (positive i))).total
example (i : Bool) := (Classical.choice (elvWeightLocalCapInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [i,i] i) (cutoff i) (positive i))).ff
example (i : Bool) (n : ℕ) := (Classical.choice (elvWeightLocalCapInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [i,i] i) (cutoff i) (positive i))).g'_mem n
example (i : Bool) := (Classical.choice (elvWeightLocalCapInverse_nonempty D Sc cut 8 i Λ rfl rfl (M [i,i] i) (cutoff i) (positive i))).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (Classical.choice (elvWeightLocalCapFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (positive i))).total
example (i : Bool) := (Classical.choice (elvWeightLocalCapFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (positive i))).ff
example (i : Bool) := (Classical.choice (elvWeightLocalCapFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (positive i))).f'_mem
example (i : Bool) (n : ℕ) := (Classical.choice (elvWeightLocalCapFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (positive i))).g'_mem n
example (i : Bool) := (Classical.choice (elvWeightLocalCapFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (positive i))).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (Classical.choice (elvWeightLocalUnitFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (le_of_eq (middle i)))).total
example (i : Bool) := (Classical.choice (elvWeightLocalCapFamily_nonempty D Sc cut 8 i Λ rfl rfl (cutoff i) (le_of_eq (middle i).symm))).total
end WeightLocalInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

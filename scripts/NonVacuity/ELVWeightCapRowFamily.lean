import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCapRowFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightCapRowFamilyConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private theorem lower (x : Bool → ℤ) (i : Bool) : (x - D.α i) + D.α i = x := sub_add_cancel _ _
private def block (i : Bool) : WeightBlocks D Λ (D.α i - Λ) := ⟨{i}, by simp⟩
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (D.α i - Λ) := fun δ =>
  ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
private def shifted (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (D.α i - Λ) := fun δ =>
  supermoduleParityObj (M i δ)
private def oddInput (i : Bool) : shifted i ⟶ M i := fun δ =>
  (supermoduleParityIso (M i δ)).hom
private theorem oddInput_mem (i : Bool) : oddInput i ∈ parity (R := ℚ) _ _ 1 := fun δ =>
  supermoduleParityIso_hom_mem (M i δ)
/-- Both parities and every cap power act on occupied output content. -/
example (i : Bool) (n : ℕ) := elvWeightCapPower_mem D Sc cut 8 i Λ (lower (D.α i - Λ) i) n
example (i : Bool) (n : ℕ) :=
  (elvWeightCapPower_block_supernatural D Sc cut 8 i Λ
    (lower (D.α i - Λ) i) (block i) n).mem (shifted i)
example (i : Bool) (n : ℕ) :=
  (elvWeightCapPower_block_supernatural D Sc cut 8 i Λ
    (lower (D.α i - Λ) i) (block i) n).naturality (oddInput_mem i)
end WeightCapRowFamilyConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightCapRowFamily
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

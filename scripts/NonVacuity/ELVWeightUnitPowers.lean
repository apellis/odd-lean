import OddMath.QuiverHecke.CyclotomicAction.ELVWeightUnitPowers
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightUnitPowersConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem lower (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem upper (i : Bool) : D.α i + D.α i = D.α i + D.α i := rfl
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
private def zeroM : ELVWeightProduct D Sc cut 8 0 (0 : Bool → ℤ) := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[]⟩))
private def zeroBlock : WeightBlocks D 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
private def oneBlock (i : Bool) : WeightBlocks D 0 (D.α i) := ⟨{i}, by simp⟩
example (i : Bool) (n : ℕ) := elvWeightUnit_dotPower_comparison D Sc cut 8 i 0
  (lower i) zeroBlock zeroM n
example (i : Bool) (n : ℕ) := elvWeightUnit_dotPower_comparison D Sc cut 8 i 0
  (upper i) (oneBlock i) (M i) n
end WeightUnitPowersConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightUnitPowers
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

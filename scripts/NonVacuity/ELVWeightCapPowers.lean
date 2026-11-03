import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCapPowers
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightCapPowersConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem lower (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
private def zeroBlock : WeightBlocks D 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
example (i : Bool) (n : ℕ) := elvWeightCounit_dotPower_comparison D Sc cut 8 i 0
  (lower i) zeroBlock (M i) n
example (i : Bool) (n : ℕ) := elvWeightCapPower_total_comparison D Sc cut 8 i 0
  (lower i) zeroBlock (M i) n
private def emptyM (i : Bool) : ELVWeightProduct D Sc (fun _ => 0) 0 0 (D.α i) := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc (fun _ => 0) 0 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (fun _ => 0) 0
      ((oldTruncateFunctor D Sc (fun _ => 0) 0).obj ⟨[i]⟩))
example (i : Bool) (n : ℕ) := elvWeightCapPower_total_comparison D Sc (fun _ => 0) 0 i 0
  (lower i) zeroBlock (emptyM i) n
end WeightCapPowersConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightCapPowers
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

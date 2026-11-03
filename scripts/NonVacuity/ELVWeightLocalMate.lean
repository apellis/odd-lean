import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightLocalMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem lower (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem upper (i : Bool) : D.α i + D.α i = D.α i + D.α i := rfl
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
/-- Every principal local-inversion field remains the selected native weight mate. -/
example (i : Bool) := elvWeightRouquierMate_eq D Sc cut 8 i 0 (lower i) (upper i)
example (i : Bool) := elvWeightRouquierMate_mem D Sc cut 8 i 0 (lower i) (upper i)
private def oneBlock (i : Bool) : WeightBlocks D 0 (D.α i) := ⟨{i}, by simp⟩
example (i : Bool) (p : ZMod 2) := elvWeightRouquierMate_app_block D Sc cut 8 i 0
  (lower i) (upper i) p (M i) (oneBlock i)
example := elvWeightRouquierMate_mem AsymmetricParameters.datum AsymmetricParameters.scalars cut 8 false 0
  (zero_add _) (rfl : AsymmetricParameters.datum.α false + AsymmetricParameters.datum.α false = _)
/-- Empty truncation is retained without a nonzero-module condition. -/
example (i : Bool) := elvWeightRouquierMate_eq D Sc (fun _ => 0) 0 i 0 (lower i) (upper i)
end WeightLocalMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

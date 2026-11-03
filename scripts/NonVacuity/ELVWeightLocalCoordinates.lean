import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightLocalCoordinatesConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private def base : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (-Λ + D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
/-- Both moving parities share the principal coordinates on an occupied intermediate block. -/
example (i : Bool) := elvWeightLocalSource_hom D Sc cut 8 i Λ rfl base (M i)
example (i : Bool) := elvWeightLocalTarget_hom D Sc cut 8 i Λ rfl rfl base (M i)
/-- Every prescribed unit and cap power uses those exact same equations. -/
example (i : Bool) (n : ℕ) := elvWeightUnitPower_localCoordinates D Sc cut 8 i Λ rfl rfl base (M i) n
example (i : Bool) (n : ℕ) := elvWeightCapPower_localCoordinates D Sc cut 8 i Λ rfl base (M i) n
end WeightLocalCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

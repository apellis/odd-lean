import OddMath.QuiverHecke.CyclotomicAction.ELVContentUnitColumnSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentUnitColumnSquareConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def input (v : List Bool) : ContentModules D Sc cut 8 (v : Multiset Bool) :=
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 (v : Multiset Bool))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))
/-- Both moving parities and every power on empty and nonempty absent-colour blocks. -/
example (i : Bool) (n : ℕ) := contentUnitDotColumn_square D Sc cut 8 ([] : List Bool) i (input []) n
example (i : Bool) (n : ℕ) := contentUnitDotColumn_square D Sc cut 8 ([!i] : List Bool) i (input [!i]) n
/-- Supported content uses the identical selected whole module charts. -/
example (i : Bool) (n : ℕ) := contentUnitDotColumn_square D Sc cut 8 ([i] : List Bool) i (input [i]) n
example (i : Bool) := contentUnitTargetIso_hom_mem D Sc cut 8 ([] : List Bool) i (input [])
example (i : Bool) := contentUnitTargetIso_inv_mem D Sc cut 8 ([!i] : List Bool) i (input [!i])
example (i : Bool) := contentUnitValueIso_hom_mem D Sc cut 8 ([i] : List Bool) (input [i])
end ContentUnitColumnSquareConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentUnitColumnSquare
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

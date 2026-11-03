import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace InductionGridCrossSquareConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def N := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut (OldCategory.mk []))
/-- Literal old quotient relations yield the negative native module crossing square. -/
example (i : Bool) := gridDoubleCrossComponent_square
  (oldContentAppend D Sc cut [] i) (oldContentAppend D Sc cut [i] i)
  (oldContentMatrixCross_supernatural D Sc cut [] i)
  (oldContentEqualCross_square D Sc cut [] i) N
/-- The equation holds as a two-morphism on the entire old input category, for both parities. -/
example (i : Bool) := inductionModuleCross_square
  (oldContentAppend D Sc cut [] i) (oldContentAppend D Sc cut [i] i)
  (oldContentMatrixCross_supernatural D Sc cut [] i)
  (oldContentEqualCross_square D Sc cut [] i)
end InductionGridCrossSquareConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

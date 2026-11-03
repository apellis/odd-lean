import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedMixedCross
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace InductionCrossComparisonConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev app (i : Bool) := truncatedAppend D Sc cut 8 [i]
private def P := supermoduleParityObj (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
  ((oldTruncateFunctor D Sc cut 8).obj ⟨[false,true]⟩))

/-- The whole generic comparison specializes to the given positive mixed quotient crossing. -/
example (i : Bool) := inductionCompOfEq_cross (app (!i)) (app i) (app i) (app (!i))
  (app (!i) ⋙ app i) (app i ⋙ app (!i)) rfl rfl
  (truncatedDistinctCross_supernatural D Sc cut 8 i (!i))
  (truncatedDistinctCross_supernatural D Sc cut 8 i (!i))
  (fun _ => by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]) P
example (i : Bool) := inductionTransform_app_self
  (app (!i) ⋙ app i) (app i ⋙ app (!i))
  (truncatedDistinctCross_supernatural D Sc cut 8 i (!i)) P
end InductionCrossComparisonConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossComparison
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace ModuleInductionSlidesConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private abbrev J (i : Bool) := append D Sc cut i
private def R (v : List Bool) := oldRepresentable D Sc cut (⟨v⟩ : OldCategory D Sc cut)
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide

/-- The literal OLD quotient supplies all source hypotheses for the first dot. -/
example (i : Bool) := transformComponent_rectangular_slide
  ((oldAppendDot_supernatural D Sc cut (!i)).whiskerRight (J i))
  (Distinct.cross_supernatural D Sc cut i (!i))
  ((oldAppendDot_supernatural D Sc cut (!i)).whiskerLeft (J i))
  (sign ℚ (D.parity (!i) * D.parity i))
  (Distinct.crossComponent_slide_first D Sc cut (ne i)) (R [false,true])
/-- The second dot uses the independently selected opposite whiskerings. -/
example (i : Bool) := transformComponent_rectangular_slide
  ((oldAppendDot_supernatural D Sc cut i).whiskerLeft (J (!i)))
  (Distinct.cross_supernatural D Sc cut i (!i))
  ((oldAppendDot_supernatural D Sc cut i).whiskerRight (J (!i)))
  (sign ℚ (D.parity (!i) * D.parity i))
  (Distinct.crossComponent_slide_last D Sc cut (ne i)) (supermoduleParityObj (R []))

private abbrev Do := CyclotomicAction.AsymmetricParameters.datum
private abbrev So := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Jo (i : Bool) := append Do So cut i
private def Ro := oldRepresentable Do So cut (⟨[false,true]⟩ : OldCategory Do So cut)
/-- Both dot and crossing are odd, so both superopposite signs are exercised. -/
example := transformComponent_rectangular_slide
  ((oldAppendDot_supernatural Do So cut true).whiskerRight (Jo false))
  (Distinct.cross_supernatural Do So cut false true)
  ((oldAppendDot_supernatural Do So cut true).whiskerLeft (Jo false))
  (sign ℚ (Do.parity true * Do.parity false))
  (Distinct.crossComponent_slide_first Do So cut (by decide : false ≠ true)) Ro
end ModuleInductionSlidesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionSlides
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

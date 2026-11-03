import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace ModuleInductionBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private abbrev J (i : Bool) := append D Sc cut i
private def R (v : List Bool) := oldRepresentable D Sc cut (⟨v⟩ : OldCategory D Sc cut)

/-- The abstract source braid is supplied by the literal old quotient,
for both moving parities and every displayed old context. -/
example (i : Bool) (v : List Bool) := transformComponent_braid ((J i ⋙ J i) ⋙ J i)
  ((equalCross_supernatural D Sc cut i).whiskerRight (J i))
  ((equalCross_supernatural D Sc cut i).whiskerLeft (J i))
  (equalCrossComponent_braid D Sc cut i) (R v)
example (i : Bool) := transformComponent_braid ((J i ⋙ J i) ⋙ J i)
  ((equalCross_supernatural D Sc cut i).whiskerRight (J i))
  ((equalCross_supernatural D Sc cut i).whiskerLeft (J i))
  (equalCrossComponent_braid D Sc cut i) (supermoduleParityObj (R [false,true]))
end ModuleInductionBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

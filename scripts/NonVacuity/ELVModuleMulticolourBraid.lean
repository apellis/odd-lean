import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourInduction
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace ModuleMulticolourBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private def N := oldRepresentable D Sc cut (⟨[false,true]⟩ : OldCategory D Sc cut)
/-- The generic source-path premise is proved by the actual OLD quotient. -/
example (i j l : Bool) (hb : ¬ (i = l ∧ i ≠ j)) :=
  transformComponent_multicolour_braid
    (tripleAppend D Sc cut i j l) (tripleAppend D Sc cut j i l)
    (tripleAppend D Sc cut j l i) (tripleAppend D Sc cut l j i)
    (tripleAppend D Sc cut i l j) (tripleAppend D Sc cut l i j)
    (triplePrefix_supernatural D Sc cut i j l)
    (tripleSuffix_supernatural D Sc cut j i l)
    (triplePrefix_supernatural D Sc cut j l i)
    (tripleSuffix_supernatural D Sc cut i j l)
    (triplePrefix_supernatural D Sc cut i l j)
    (tripleSuffix_supernatural D Sc cut l i j)
    (tripleCross_braid D Sc cut i j l hb) N
end ModuleMulticolourBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleMulticolourBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

import OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedGridMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NormalizedGridMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private def input (i : Bool) : ContentModules D Sc cut 8 ({i} : Multiset Bool) :=
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 {i})).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
private theorem lower (i : Bool) : (0 : Multiset Bool) + ([i] : Multiset Bool) = {i} := by simp
private theorem upper (i : Bool) : ({i} : Multiset Bool) + ([i] : Multiset Bool) = {i,i} := by simp
example (i : Bool) := contentTargetsGridCross_supernatural D Sc cut 8 0 {i} {i,i} i (lower i) (upper i)
/-- Both moving parities retain the literal whole module mate and all endpoint certificates. -/
example (i : Bool) := normalizedContentTargetsMate_eq_grid D Sc cut 8 0 {i} {i,i} i
  (lower i) (upper i) (input i)
end NormalizedGridMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedGridMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

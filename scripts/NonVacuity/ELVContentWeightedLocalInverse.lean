import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor BalancedInduction
namespace ContentWeightedLocalInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def input (i : Bool) := supermoduleParityObj
  (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
    ((oldTruncateFunctor D Sc cut 8).obj ⟨[!i]⟩))
private theorem emptySign (i : Bool) : 0 ≤ contentCrossingHeight D cut i 0 := by
  simp [contentCrossingHeight]
private theorem otherSign (i : Bool) :
    0 ≤ contentCrossingHeight D cut i ([!i] : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def emptyData (i : Bool) := weightedContentLocalInverseFrom D Sc cut 8 i (input i) 0 (emptySign i)
private def otherData (i : Bool) := weightedContentLocalInverseFrom D Sc cut 8 i (input i) [!i] (otherSign i)
/-- Both parities retain constructed inverse rows on absent-colour output contents. -/
example (i : Bool) := (emptyData i).total
example (i : Bool) := (emptyData i).ff
example (i : Bool) := (emptyData i).f'_mem
example (i : Bool) (n : ℕ) := (emptyData i).g'_mem n
example (i : Bool) := (otherData i).total
example (i : Bool) := (otherData i).ff
example (i : Bool) := (otherData i).f'_mem
example (i : Bool) (n : ℕ) := (otherData i).g'_mem n
example (i : Bool) := (emptyData i).fg 0 (by cases i <;> decide)
example (i : Bool) := (emptyData i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (otherData i).gf 0 (by cases i <;> decide)
example (i : Bool) := (otherData i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
end ContentWeightedLocalInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedLocalInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open BalancedInduction CyclotomicCrossingTensor
namespace ContentAbsentUnitInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def input (v : List Bool) : ContentModules D Sc cut 8 (v : Multiset Bool) :=
  supermoduleParityObj ((restriction (contentInclusion D Sc cut 8 (v : Multiset Bool))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))
private def emptyInverse (i : Bool) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cut 8 0 i (by simp) (input []))
private def otherInverse (i : Bool) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cut 8 [!i] i (by cases i <;> decide) (input [!i]))
/-- The constructed unit inverse retains FE and all given columns on absent contents. -/
example (i : Bool) := (emptyInverse i).total
example (i : Bool) := (emptyInverse i).ff
example (i : Bool) := (emptyInverse i).f'_mem
example (i : Bool) (n : ℕ) := (emptyInverse i).g'_mem n
example (i : Bool) := (otherInverse i).total
example (i : Bool) := (otherInverse i).ff
example (i : Bool) := (otherInverse i).f'_mem
example (i : Bool) (n : ℕ) := (otherInverse i).g'_mem n
example (i : Bool) := (emptyInverse i).fg 0 (by cases i <;> decide)
example (i : Bool) := (emptyInverse i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (otherInverse i).gf 0 (by cases i <;> decide)
example (i : Bool) := (otherInverse i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
private def emptyZeroInput : ContentModules D Sc (fun _ => 0) 0 0 :=
  (restriction (contentInclusion D Sc (fun _ => 0) 0 0)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (fun _ => 0) 0
      ((oldTruncateFunctor D Sc (fun _ => 0) 0).obj ⟨[]⟩))
/-- FE vanishing at the zero-count boundary is derived from the constructed inverse. -/
example (i : Bool) := contentAbsentUnitTarget_isZero D Sc (fun _ => 0) 0 0 i
  (by simp) emptyZeroInput (by simp [contentUnitCount, contentCrossingHeight])
end ContentAbsentUnitInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

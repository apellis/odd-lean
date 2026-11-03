import OddMath.SKM.AugmentedInverseProfile
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction CyclotomicCrossingTensor BalancedInduction
namespace AugmentedInverseProfileConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def M (v : List Bool) := supermoduleParityObj
  (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
    ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩))
private def emptyInput : ContentModules D Sc cut 8 0 :=
  (restriction (contentInclusion D Sc cut 8 0)).obj (M [])
private def columnInverse (i : Bool) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cut 8 0 i (by simp) emptyInput)
private theorem negative (i : Bool) : contentCrossingHeight D cut i ([i,i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def rowInverse (i : Bool) := weightedContentLocalInverseTo D Sc cut 8 i (M [i,i,i]) [i,i,i] (negative i)
/-- The profile conversion preserves the constructed principal and every inverse entry literally. -/
example (i : Bool) := (columnInverse i).mulProfile_f'
example (i : Bool) (n : ℕ) := (columnInverse i).mulProfile_g' n
example (i : Bool) := (rowInverse i).mulProfile_f'
example (i : Bool) (n : ℕ) := (rowInverse i).mulProfile_g' n
/-- Both moving parities retain the exact finite inverse equations and all graded rows/columns. -/
example (i : Bool) := (columnInverse i).mulProfile.total
example (i : Bool) := (columnInverse i).mulProfile.ff
example (i : Bool) (n : ℕ) := (columnInverse i).mulProfile.g'_mem n
example (i : Bool) := (columnInverse i).mulProfile.gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (rowInverse i).mulProfile.total
example (i : Bool) := (rowInverse i).mulProfile.ff
example (i : Bool) (n : ℕ) := (rowInverse i).mulProfile.g'_mem n
example (i : Bool) := (rowInverse i).mulProfile.gg 1 0 (by cases i <;> decide) (by cases i <;> decide)
end AugmentedInverseProfileConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.AugmentedInverseProfile
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

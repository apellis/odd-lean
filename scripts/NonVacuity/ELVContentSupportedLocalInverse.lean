import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction CyclotomicCrossingTensor BalancedInduction
namespace ContentSupportedLocalInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def M (v : List Bool) : ContentModules D Sc cut 8 (v : Multiset Bool) :=
  supermoduleParityObj ((restriction (contentInclusion D Sc cut 8 (v : Multiset Bool))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))
private theorem positive (i : Bool) : 0 ≤ contentCrossingHeight D cut i ([i] : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem negative (i : Bool) : contentCrossingHeight D cut i ([i,i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem middle (i : Bool) : contentCrossingHeight D cut i ([i,i] : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def fromInverse (i : Bool) := Classical.choice
  (contentSupportedLocalInverseFrom_nonempty D Sc cut 8 0 i (M [i]) (positive i))
private def toInverse (i : Bool) := Classical.choice
  (contentSupportedLocalInverseTo_nonempty D Sc cut 8 [i,i] i (M [i,i,i]) (negative i))
private def zeroFrom (i : Bool) := Classical.choice
  (contentSupportedLocalInverseFrom_nonempty D Sc cut 8 [i] i (M [i,i]) (le_of_eq (middle i).symm))
private def zeroTo (i : Bool) := Classical.choice
  (contentSupportedLocalInverseTo_nonempty D Sc cut 8 [i] i (M [i,i]) (le_of_eq (middle i)))
/-- The selected unit and cap inverses retain both moving parities and all finite fields. -/
example (i : Bool) := (fromInverse i).total
example (i : Bool) := (fromInverse i).ff
example (i : Bool) := (fromInverse i).f'_mem
example (i : Bool) (n : ℕ) := (fromInverse i).g'_mem n
example (i : Bool) := (fromInverse i).fg 0 (by cases i <;> decide)
example (i : Bool) := (fromInverse i).gf 1 (by cases i <;> decide)
example (i : Bool) := (fromInverse i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (toInverse i).total
example (i : Bool) := (toInverse i).ff
example (i : Bool) := (toInverse i).f'_mem
example (i : Bool) (n : ℕ) := (toInverse i).g'_mem n
example (i : Bool) := (toInverse i).fg 0 (by cases i <;> decide)
example (i : Bool) := (toInverse i).gf 1 (by cases i <;> decide)
example (i : Bool) := (toInverse i).gg 1 0 (by cases i <;> decide) (by cases i <;> decide)
/-- Both directions also retain the empty finite window at zero categorical height. -/
example (i : Bool) := (zeroFrom i).total
example (i : Bool) := (zeroFrom i).ff
example (i : Bool) := (zeroTo i).total
example (i : Bool) := (zeroTo i).ff
/-- Stored successor contents retain the same constructed inverse in both orientations. -/
example (i : Bool) := contentTargetsLocalInverseFrom_nonempty D Sc cut 8 0 i
  [i] [i,i] rfl rfl (M [i]) (positive i)
example (i : Bool) := contentTargetsLocalInverseTo_nonempty D Sc cut 8 [i,i] i
  [i,i,i] [i,i,i,i] rfl rfl (M [i,i,i]) (negative i)
end ContentSupportedLocalInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedLocalInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

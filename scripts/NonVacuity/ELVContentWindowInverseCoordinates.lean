import OddMath.QuiverHecke.CyclotomicAction.ELVContentWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficientFaithful
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction CyclotomicCrossingTensor BalancedInduction
namespace ContentWindowInverseCoordinatesConsumer
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
private def fromInverse (i : Bool) := Classical.choice
  (contentSupportedLocalInverseFrom_nonempty D Sc cut 8 0 i (M [i]) (positive i))
private def toInverse (i : Bool) := Classical.choice
  (contentSupportedLocalInverseTo_nonempty D Sc cut 8 [i,i] i (M [i,i,i]) (negative i))
/-- Every finite `g'` of the chosen unit record, for both moving parities. -/
example (i : Bool) (m : Fin (contentUnitCount D cut i ([i] : Multiset Bool))) :=
  contentSupportedLocalInverseFrom_window D Sc cut 8 0 i
    (M [i]) (fromInverse i) (positive i) m.val m.isLt
/-- Every finite `g'` of the chosen cap record, for both moving parities. -/
example (i : Bool) (m : Fin (contentCapCount D cut i ([i,i,i] : Multiset Bool))) :=
  contentSupportedLocalInverseTo_window D Sc cut 8 [i,i] i
    (M [i,i,i]) (toInverse i) (negative i) m.val m.isLt
/-- The explicit successor-content charts retain all finite windows. -/
example (i : Bool) (m : Fin (contentUnitCount D cut i ([i] : Multiset Bool))) :=
  contentTargetsLocalInverseFrom_window D Sc cut 8 0 i
    [i] [i,i] rfl rfl (M [i]) (fromInverse i) (positive i) m.val m.isLt
example (i : Bool) (m : Fin (contentCapCount D cut i ([i,i,i] : Multiset Bool))) :=
  contentTargetsLocalInverseTo_window D Sc cut 8 [i,i] i
    [i,i,i] [i,i,i,i] rfl rfl (M [i,i,i]) (toInverse i) (negative i) m.val m.isLt
end ContentWindowInverseCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentWindowInverseCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

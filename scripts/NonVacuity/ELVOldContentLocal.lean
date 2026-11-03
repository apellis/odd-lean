import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentLocal
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace OldContentLocalConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def unitData (i : Bool) := oldContentLoc D Sc cut [] i
private def capData (i : Bool) := oldContentLoc D Sc cut [i,i] i
private def zeroData (i : Bool) := oldContentLoc D Sc (fun _ => 2) [] i
/-- Both dot degrees, crossing degrees, and slides are supplied by literal old maps. -/
example (i : Bool) := (unitData i).dot₁_mem
example (i : Bool) := (unitData i).dot₂_mem
example (i : Bool) := (unitData i).cross_mem
example (i : Bool) := (unitData i).slide_left
example (i : Bool) := (unitData i).slide_right
example (i : Bool) := oldContentLoc_cross_square D Sc cut [] i
/-- The finite inverses use both height directions and the zero-height overlap. -/
example (i : Bool) := ((unitData i).invNeg (by cases i <;> decide)).total
example (i : Bool) := ((capData i).invPos (by cases i <;> decide)).total
example (i : Bool) := ((zeroData i).invNeg (by cases i <;> decide)).total
example (i : Bool) := ((zeroData i).invPos (by cases i <;> decide)).total
example (i : Bool) := ((unitData i).invNeg (by cases i <;> decide)).gg 0 1
  (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := ((capData i).invPos (by cases i <;> decide)).gg 0 1
  (by cases i <;> decide) (by cases i <;> decide)
end OldContentLocalConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridLocal,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOldContentLocal] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"

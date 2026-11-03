import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace InductionGridRelationsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
/-- Both literal source slides act on the whole old module input category, in both parities. -/
example (ν : List Bool) (i : Bool) := inductionModuleCross_slide_left
  (oldContentAppend D Sc cut ν i) (oldContentAppend D Sc cut (i::ν) i)
  (oldContentMatrixCross_supernatural D Sc cut ν i)
  (oldContentAppendDot_supernatural D Sc cut ν i)
  (oldContentAppendDot_supernatural D Sc cut (i::ν) i)
  (by
    intro s
    have h := oldContentEqualCross_slideLeft D Sc cut ν i s
    rw [koszulSign_smul (R := ℚ)] at h
    convert! h using 1)
example (ν : List Bool) (i : Bool) := inductionModuleCross_slide_right
  (oldContentAppend D Sc cut ν i) (oldContentAppend D Sc cut (i::ν) i)
  (oldContentMatrixCross_supernatural D Sc cut ν i)
  (oldContentAppendDot_supernatural D Sc cut ν i)
  (oldContentAppendDot_supernatural D Sc cut (i::ν) i)
  (by
    intro s
    have h := oldContentEqualCross_slideRight D Sc cut ν i s
    rw [koszulSign_smul (R := ℚ)] at h
    convert! h using 1)
end InductionGridRelationsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRelations
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

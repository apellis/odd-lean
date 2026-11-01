import NonVacuity.ELVCoefficientCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingHeight
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.QuiverHecke ELVOld CyclotomicCrossingTensor
open ELVCoefficientCategoryConsumer

/-- Odd rank one, full coefficient algebra and zero Cartan height. -/
def zeroHeightCrossing :
    Source datum scalars (fun _ => 2) () [()] [()] ≃ₗ[ℚ]
      Old datum scalars (fun _ => 2) [(), ()] [(), ()] := by
  apply toCyclotomicEquiv_zero_height datum scalars (fun _ => 2) 0 oddColour [()]
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 2) () [()]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, oddColour] at h ⊢
  omega

example (z : Source datum scalars (fun _ => 2) () [()] [()]) :
    zeroHeightCrossing.symm (zeroHeightCrossing z) = z :=
  zeroHeightCrossing.symm_apply_apply z

example (z : Old datum scalars (fun _ => 2) [(), ()] [(), ()]) :
    zeroHeightCrossing (zeroHeightCrossing.symm z) = z :=
  zeroHeightCrossing.apply_symm_apply z

example : Function.Injective (toCyclotomic datum scalars (fun _ => 4) () [()] [()]) := by
  apply toCyclotomic_injective_of_nonnegative_height datum scalars (fun _ => 4) 0 oddColour [()]
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 4) () [()]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, oddColour] at h ⊢
  omega

example : Function.Surjective (toCyclotomic datum scalars (fun _ => 1) () [()] [()]) := by
  apply toCyclotomic_surjective_of_nonpositive_height datum scalars (fun _ => 1) 0 oddColour [()]
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 1) () [()]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, oddColour] at h ⊢
  omega

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCrossingHeight
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"

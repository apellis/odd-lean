import NonVacuity.ELVCoefficientCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedSourceLinearEquiv
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace ShiftedSourceLinearEquivConsumer
open OddMath OddMath.QuiverHecke ELVOld CyclotomicCrossingTensor
open ELVCoefficientCategoryConsumer

/-- The actual induced-restricted representable at the odd rank-one corner. -/
abbrev ActualSource :=
  ((BalancedInduction.induction (append datum scalars (fun _ => 2) ())).obj
    ((BalancedInduction.restriction (append datum scalars (fun _ => 2) ())).obj
      (oldRepresentable datum scalars (fun _ => 2)
        (⟨[()]⟩ : OldCategory datum scalars (fun _ => 2))))).obj
          (⟨[()]⟩ : OldCategory datum scalars (fun _ => 2))

def canonical : ActualSource ≃ₗ[ℚ] Source datum scalars (fun _ => 2) () [()] [()] :=
  shiftedSourceCanonicalEquiv datum scalars (fun _ => 2) oddColour [()] [()]

example (x : ActualSource) : canonical.symm (canonical x) = x :=
  canonical.symm_apply_apply x

example (z : Source datum scalars (fun _ => 2) () [()] [()]) :
    canonical (canonical.symm z) = z :=
  canonical.apply_symm_apply z

example (x : ActualSource) :
    (shiftedSourceCounit datum scalars (fun _ => 2) () [()]).total
      (⟨[()]⟩ : OldCategory datum scalars (fun _ => 2))
      ((coefficientOneSourceEquiv datum scalars (fun _ => 2) oddColour [()] [()]).symm
        (canonical x)) =
      ((BalancedInduction.adjunctionCounit (append datum scalars (fun _ => 2) ())).app
        (oldRepresentable datum scalars (fun _ => 2)
          (⟨[()]⟩ : OldCategory datum scalars (fun _ => 2)))).total
            (⟨[()]⟩ : OldCategory datum scalars (fun _ => 2)) x :=
  shiftedSourceCanonicalEquiv_counit datum scalars (fun _ => 2) oddColour [()] [()] x

end ShiftedSourceLinearEquivConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedSourceLinearEquiv
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"

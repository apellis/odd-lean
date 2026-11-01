import NonVacuity.SerreComplex
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedSourceLinearEquiv
import Lean.Util.CollectAxioms

noncomputable section
namespace ShiftedSourceLinearEquivConsumer
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke ELVOld CyclotomicCrossingTensor
open NonVacuity.SerreComplex

def movingOdd : {i : Bool // datum.parity i = 1} := ⟨true, rfl⟩
def sourceWord : List Bool := [false, true]
def targetWord : List Bool := [true, false]
abbrev ModelSource :=
  ((BalancedInduction.induction (append datum scalars (fun _ => 3) movingOdd.1)).obj
    ((BalancedInduction.restriction (append datum scalars (fun _ => 3) movingOdd.1)).obj
      (oldRepresentable datum scalars (fun _ => 3)
        (⟨sourceWord⟩ : OldCategory datum scalars (fun _ => 3))))).obj
          (⟨targetWord⟩ : OldCategory datum scalars (fun _ => 3))
abbrev PrescribedSource := Source datum scalars (fun _ => 3) movingOdd.1 sourceWord targetWord

def canonical : ModelSource ≃ₗ[ℚ] PrescribedSource :=
  shiftedSourceCanonicalEquiv datum scalars (fun _ => 3) movingOdd sourceWord targetWord

example (z : ModelSource) : canonical.symm (canonical z) = z := canonical.symm_apply_apply z
example (z : PrescribedSource) : canonical (canonical.symm z) = z := canonical.apply_symm_apply z

example (z : ModelSource) :
    (shiftedSourceCounit datum scalars (fun _ => 3) movingOdd.1 sourceWord).total
      (⟨targetWord⟩ : OldCategory datum scalars (fun _ => 3))
      ((coefficientOneSourceEquiv datum scalars (fun _ => 3) movingOdd sourceWord targetWord).symm
        (canonical z)) =
    ((BalancedInduction.adjunctionCounit (append datum scalars (fun _ => 3) movingOdd.1)).app
      (oldRepresentable datum scalars (fun _ => 3)
        (⟨sourceWord⟩ : OldCategory datum scalars (fun _ => 3)))).total
          (⟨targetWord⟩ : OldCategory datum scalars (fun _ => 3)) z :=
  shiftedSourceCanonicalEquiv_counit datum scalars (fun _ => 3)
    movingOdd sourceWord targetWord z

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


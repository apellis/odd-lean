import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMateTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace InductionMateTensorConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num



example (i : Bool) (s t : OldCategory mixedDatum mixedScalars (fun _ => 4))
    (g : (append mixedDatum mixedScalars (fun _ => 4) i).obj s ⟶ t)
    (b : (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
      (⟨[false, true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))).obj
        ((append mixedDatum mixedScalars (fun _ => 4) i).obj s)) :
    (BalancedInduction.orderedMateComponent
      (append mixedDatum mixedScalars (fun _ => 4) i)
      (equalCross_supernatural mixedDatum mixedScalars (fun _ => 4) i)
      (oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩)).total t
      (BalancedInduction.tensor (append mixedDatum mixedScalars (fun _ => 4) i)
        ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) i)).obj
          (oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩)).toFunctor s g b) =
    -BalancedInduction.tensor (append mixedDatum mixedScalars (fun _ => 4) i)
      (oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩).toFunctor
      ((append mixedDatum mixedScalars (fun _ => 4) i).obj s)
      (equalCrossComponent mixedDatum mixedScalars (fun _ => 4) i s ≫
        twist ℚ (mixedDatum.parity i * mixedDatum.parity i)
          ((append mixedDatum mixedScalars (fun _ => 4) i).map g)) b :=
  BalancedInduction.orderedMateComponent_total_tensor
    (append mixedDatum mixedScalars (fun _ => 4) i)
    (equalCross_supernatural mixedDatum mixedScalars (fun _ => 4) i) _ s t g b

end InductionMateTensorConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionMateTensor] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

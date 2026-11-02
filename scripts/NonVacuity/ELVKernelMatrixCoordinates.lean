import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace KernelMatrixCoordinatesConsumer
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



abbrev C := OldCategory mixedDatum mixedScalars (fun _ => 4)

example (i : Bool) :
    actualMateKernelLinear mixedDatum mixedScalars (fun _ => 4) i
      (Opposite.op (⟨[false, true]⟩ : C)) (⟨[true, false]⟩ : C) =
      kernelMateRowLinear mixedDatum mixedScalars (fun _ => 4) i
        (Opposite.op (⟨[false, true]⟩ : C)) (⟨[true, false]⟩ : C) :=
  actualMateKernelLinear_eq_row mixedDatum mixedScalars (fun _ => 4) i _ _

example (i : Bool)
    (z : (BalancedKernelTensor.piKernel
      (positiveKernelFamily mixedDatum mixedScalars (fun _ => 4) i 0 (⟨[true, false]⟩ : C))).obj
        (Opposite.op (⟨[false, true]⟩ : C))) :
    (positiveKernelCoordinates mixedDatum mixedScalars (fun _ => 4) i 0
      (Opposite.op (⟨[false, true]⟩ : C)) (⟨[true, false]⟩ : C)).symm
        (positiveKernelCoordinates mixedDatum mixedScalars (fun _ => 4) i 0
          (Opposite.op (⟨[false, true]⟩ : C)) (⟨[true, false]⟩ : C) z) = z :=
  LinearEquiv.symm_apply_apply _ z

example (i : Bool)
    (z : (BalancedKernelTensor.piKernel
      (negativeKernelFamily mixedDatum mixedScalars (fun _ => 4) i 3 (⟨[true, false]⟩ : C))).obj
        (Opposite.op (⟨[false, true]⟩ : C))) :
    (negativeKernelCoordinates mixedDatum mixedScalars (fun _ => 4) i 3
      (Opposite.op (⟨[false, true]⟩ : C)) (⟨[true, false]⟩ : C)).symm
        (negativeKernelCoordinates mixedDatum mixedScalars (fun _ => 4) i 3
          (Opposite.op (⟨[false, true]⟩ : C)) (⟨[true, false]⟩ : C) z) = z :=
  LinearEquiv.symm_apply_apply _ z

end KernelMatrixCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

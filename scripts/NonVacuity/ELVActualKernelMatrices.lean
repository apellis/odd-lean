import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ActualKernelMatricesConsumer
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

example (i : Bool)
    (z : IndResKernel.Component (k := ℚ) (append mixedDatum mixedScalars (fun _ => 4) i)
      (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C)) :
    (actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 4) i 2
      (⟨[false, true]⟩ : C)).app (Opposite.op (⟨[true, false]⟩ : C)) z none =
    actualMateKernelComponent mixedDatum mixedScalars (fun _ => 4) i
      (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) z :=
  actualNegativeKernelMap_none mixedDatum mixedScalars (fun _ => 4) i 2
    (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) z

example (i : Bool)
    (z : IndResKernel.Component (k := ℚ) (append mixedDatum mixedScalars (fun _ => 4) i)
      (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C)) :
    (actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 4) i 2
      (⟨[false, true]⟩ : C)).app (Opposite.op (⟨[true, false]⟩ : C)) z (some 1) =
    actualCapKernelComponent mixedDatum mixedScalars (fun _ => 4) i 1
      (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) z :=
  actualNegativeKernelMap_some mixedDatum mixedScalars (fun _ => 4) i 2
    (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) 1 z

example (i : Bool)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily mixedDatum mixedScalars (fun _ => 4)
      i 2 (⟨[false, true]⟩ : C))).obj (Opposite.op (⟨[true, false]⟩ : C))) :
    (actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 4) i 2
      (⟨[false, true]⟩ : C)).app (Opposite.op (⟨[true, false]⟩ : C)) z =
    actualMateKernelComponent mixedDatum mixedScalars (fun _ => 4) i
      (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) (z none) +
      ∑ r : Fin 2, actualUnitKernelComponent mixedDatum mixedScalars (fun _ => 4) i r.val
        (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) (z (some r)) :=
  actualPositiveKernelMap_apply mixedDatum mixedScalars (fun _ => 4) i 2
    (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) z

end ActualKernelMatricesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

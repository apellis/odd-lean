import OddMath.QuiverHecke.CyclotomicAction.ELVMateKernelNaturality
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace MateKernelNaturalityConsumer
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
    (a : (⟨[false, true]⟩ : C) ⟶ (⟨[true, false]⟩ : C))
    (z : IndResKernel.Component (k := ℚ) (append mixedDatum mixedScalars (fun _ => 4) i)
      (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C)) :
    actualMateKernelComponent mixedDatum mixedScalars (fun _ => 4) i
      (⟨[false, true]⟩ : C) (⟨[false, true]⟩ : C)
      (IndResKernel.precompose (k := ℚ) (append mixedDatum mixedScalars (fun _ => 4) i)
        a (⟨[false, true]⟩ : C) z) =
    (append mixedDatum mixedScalars (fun _ => 4) i).map a ≫
      actualMateKernelComponent mixedDatum mixedScalars (fun _ => 4) i
        (⟨[true, false]⟩ : C) (⟨[false, true]⟩ : C) z :=
  LinearMap.congr_fun (actualMateKernelComponent_precompose mixedDatum mixedScalars (fun _ => 4)
    i a (⟨[false, true]⟩ : C)) z

example (i : Bool) (v s t : C)
    (g : (append mixedDatum mixedScalars (fun _ => 4) i).obj s ⟶ t)
    (b : v ⟶ (append mixedDatum mixedScalars (fun _ => 4) i).obj s) :
    actualMateKernelComponent mixedDatum mixedScalars (fun _ => 4) i v t
      (BalancedInduction.tensor (append mixedDatum mixedScalars (fun _ => 4) i)
        ((append mixedDatum mixedScalars (fun _ => 4) i) ⋙ IndResKernel.homModule (k := ℚ) v) s g b) =
    -((append mixedDatum mixedScalars (fun _ => 4) i).map b ≫
      equalCrossComponent mixedDatum mixedScalars (fun _ => 4) i s ≫
      twist ℚ (mixedDatum.parity i) ((append mixedDatum mixedScalars (fun _ => 4) i).map g)) :=
  actualMateKernelComponent_tensor mixedDatum mixedScalars (fun _ => 4) i v s t g b

end MateKernelNaturalityConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVMateKernelNaturality
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

import OddMath.QuiverHecke.CyclotomicAction.ELVKernelOffContentMatrices
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace KernelOffContentMatricesConsumer
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





example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 2) true 3
    (⟨[true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualPositiveKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    true 3 ⟨[false]⟩ ⟨[true]⟩ (by decide)

example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 2) true 0
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualPositiveKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    true 0 ⟨[]⟩ ⟨[false,true]⟩ (by decide)

example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 2) false 3
    (⟨[true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualPositiveKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    false 3 ⟨[false]⟩ ⟨[true]⟩ (by decide)

example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 2) false 0
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualPositiveKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    false 0 ⟨[]⟩ ⟨[false,true]⟩ (by decide)

example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 2) true 3
    (⟨[true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualNegativeKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    true 3 ⟨[false]⟩ ⟨[true]⟩ (by decide)

example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 2) true 0
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualNegativeKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    true 0 ⟨[]⟩ ⟨[false,true]⟩ (by decide)

example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 2) false 3
    (⟨[true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualNegativeKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    false 3 ⟨[false]⟩ ⟨[true]⟩ (by decide)

example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 2) false 0
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)))) :=
  actualNegativeKernelMap_bijective_of_content_ne mixedDatum mixedScalars (fun _ => 2)
    false 0 ⟨[]⟩ ⟨[false,true]⟩ (by decide)

end KernelOffContentMatricesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelOffContentMatrices
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

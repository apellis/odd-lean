import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedExtension
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentSupportedExtensionConsumer
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

example (ν : List Bool)
    (M : Superfunctor ℚ (OldContentCategory mixedDatum mixedScalars (fun _ => 4) ν) (SVec ℚ)) :
    OldContentSupported mixedDatum mixedScalars (fun _ => 4) ν
      (BalancedInduction.induced (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) ν) M) :=
  oldContentExtension_supported mixedDatum mixedScalars (fun _ => 4) ν M

example (ν : List Bool)
    (N : Superfunctor ℚ C (SVec ℚ))
    (hN : OldContentSupported mixedDatum mixedScalars (fun _ => 4) ν N) :
    BalancedInduction.induced (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) ν)
      ((BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) ν)).obj N) ≅ N :=
  supportedContentCounitIso mixedDatum mixedScalars (fun _ => 4) ν N hN

private def rep : Superfunctor ℚ C (SVec ℚ) :=
  oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩
private abbrev inc := oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [true, false]
private abbrev block := (BalancedInduction.restriction inc).obj rep
private abbrev extension := BalancedInduction.induced inc block

example : BalancedInduction.induced inc ((BalancedInduction.restriction inc).obj extension) ≅
    extension :=
  supportedContentCounitIso mixedDatum mixedScalars (fun _ => 4) [true, false] extension
    (oldContentExtension_supported mixedDatum mixedScalars (fun _ => 4) [true, false] block)

end ContentSupportedExtensionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedExtension
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionExtension
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentRestrictionExtensionConsumer
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

example (i : Bool) (ν : List Bool)
    (N : Superfunctor ℚ
      (OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: ν)) (SVec ℚ)) :
    BalancedInduction.induced (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) ν)
      ((BalancedInduction.restriction (oldContentAppend mixedDatum mixedScalars (fun _ => 4) ν i)).obj N) ≅
    (BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) i)).obj
      (BalancedInduction.induced (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) (i :: ν)) N) :=
  oldContentRestrictionExtensionIso mixedDatum mixedScalars (fun _ => 4) ν i N

private def rep : Superfunctor ℚ C (SVec ℚ) :=
  oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩

example (i : Bool) :=
  oldContentRestrictionExtensionIso mixedDatum mixedScalars (fun _ => 4) [] i
    ((BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [i])).obj rep)

end ContentRestrictionExtensionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionExtension
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendTensor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentAppendTensorConsumer
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
    (M : Superfunctor ℚ (OldContentCategory mixedDatum mixedScalars (fun _ => 4) ν) (SVec ℚ))
    (s : OldContentCategory mixedDatum mixedScalars (fun _ => 4) ν)
    (t : OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: ν)) (w : C)
    (h : t.obj ⟶ w)
    (g : (append mixedDatum mixedScalars (fun _ => 4) i).obj s.obj ⟶ t.obj) (b : M.obj s) :=
  oldContentAppendExtensionIso_tensor mixedDatum mixedScalars (fun _ => 4) ν i M s t w h g b

private abbrev v : C := ⟨[false, true]⟩
private abbrev source : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true] :=
  ⟨v, List.Perm.refl _⟩
private def block : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true]) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [false, true])).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4) v)
private def unitVector : block.obj source := by
  change v ⟶ v
  exact 𝟙 v

example (i : Bool) := oldContentAppendExtensionIso_tensor
  mixedDatum mixedScalars (fun _ => 4) [false, true] i block source
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i).obj source)
  ((append mixedDatum mixedScalars (fun _ => 4) i).obj v) (𝟙 _) (𝟙 _) unitVector

example (i : Bool) := oldContentAppendExtensionIso_unit_tensor
  mixedDatum mixedScalars (fun _ => 4) [false, true] i block source
  ((append mixedDatum mixedScalars (fun _ => 4) i).obj v) (𝟙 _) unitVector

end ContentAppendTensorConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendTensor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

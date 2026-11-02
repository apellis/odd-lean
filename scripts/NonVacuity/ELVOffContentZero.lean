import OddMath.QuiverHecke.CyclotomicAction.ELVOffContentZero
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace OffContentZeroConsumer
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

private theorem mismatch : (([false] : List Bool) : Multiset Bool) ≠
    (([true] : List Bool) : Multiset Bool) := by decide

example (f : Old mixedDatum mixedScalars (fun _ => 4) [false] [true]) : f = 0 :=
  old_eq_zero_of_content_ne mixedDatum mixedScalars (fun _ => 4) mismatch f

example (i : Bool)
    (f : (append mixedDatum mixedScalars (fun _ => 4) i).obj (⟨[false]⟩ : C) ⟶
      (append mixedDatum mixedScalars (fun _ => 4) i).obj (⟨[true]⟩ : C)) : f = 0 :=
  append_hom_eq_zero_of_content_ne mixedDatum mixedScalars (fun _ => 4) i mismatch f

example (i : Bool)
    (z : IndResKernel.Component (k := ℚ) (append mixedDatum mixedScalars (fun _ => 4) i)
      (⟨[false]⟩ : C) (⟨[true]⟩ : C)) : z = 0 :=
  indResKernel_eq_zero_of_content_ne mixedDatum mixedScalars (fun _ => 4)
    (append mixedDatum mixedScalars (fun _ => 4) i) mismatch z

example (i : Bool) :
    Subsingleton (IndResKernel.Component (k := ℚ) (append mixedDatum mixedScalars (fun _ => 4) i)
      (⟨[false]⟩ : C) (⟨[true]⟩ : C)) :=
  indResKernel_subsingleton_of_content_ne mixedDatum mixedScalars (fun _ => 4)
    (append mixedDatum mixedScalars (fun _ => 4) i) mismatch

example (z : IndResKernel.Component (k := ℚ) (𝟭 C) (⟨[false]⟩ : C) (⟨[true]⟩ : C)) : z = 0 :=
  indResKernel_eq_zero_of_content_ne mixedDatum mixedScalars (fun _ => 4) (𝟭 C) mismatch z

end OffContentZeroConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffContentZero
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

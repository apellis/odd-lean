import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFChartTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentEFChartTensorsConsumer
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

private abbrev v : C := ⟨[false, true]⟩
private abbrev source : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true] :=
  ⟨v, List.Perm.refl _⟩
private def block : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true]) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [false, true])).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4) v)
private def upperBlock (i : Bool) : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: [false, true])) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) (i :: [false, true]))).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
      ((append mixedDatum mixedScalars (fun _ => 4) i).obj v))

private def upperVector (i : Bool) :
    (upperBlock i).obj ((oldContentAppend mixedDatum mixedScalars (fun _ => 4)
      [false, true] i).obj source) := by
  change (append mixedDatum mixedScalars (fun _ => 4) i).obj v ⟶
    (append mixedDatum mixedScalars (fun _ => 4) i).obj v
  exact 𝟙 _

example (i : Bool) (t : OldContentCategory mixedDatum mixedScalars (fun _ => 4)
    (i :: [false, true]))
    (g : (append mixedDatum mixedScalars (fun _ => 4) i).obj v ⟶ t.obj)
    (b : block.obj source) :=
  oldContentAppendRestrictionLinear_tensor mixedDatum mixedScalars (fun _ => 4)
    [false, true] i block source t g b

example (i : Bool) := oldContentEFRestrictionNaturalIso_hom_app
  mixedDatum mixedScalars (fun _ => 4) [false, true] i (upperBlock i)

example (i : Bool) := oldContentEFRestrictionLinear_tensor
  mixedDatum mixedScalars (fun _ => 4) [false, true] i (upperBlock i) source
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i).obj source)
  (oldAppendDotComponent mixedDatum mixedScalars (fun _ => 4) i v) (upperVector i)

private def emptySource : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [] :=
  ⟨⟨[]⟩, List.Perm.refl _⟩
private def vacuumUpper (i : Bool) : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) [i]) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [i])).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[i]⟩)
private def vacuumVector (i : Bool) :
    (vacuumUpper i).obj ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [] i).obj emptySource) := by
  change (⟨[i]⟩ : C) ⟶ (⟨[i]⟩ : C)
  exact 𝟙 _

example (i : Bool) := oldContentEFRestrictionLinear_tensor
  mixedDatum mixedScalars (fun _ => 4) [] i (vacuumUpper i) emptySource
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [] i).obj emptySource)
  (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj emptySource.obj)) (vacuumVector i)

end ContentEFChartTensorsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentEFChartTensors
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

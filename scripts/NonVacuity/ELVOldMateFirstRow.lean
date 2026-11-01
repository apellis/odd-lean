import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateFirstRow
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace OldMateFirstRowConsumer
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



private def oddColour : {j : Bool // mixedDatum.parity j = 1} := ⟨true, rfl⟩

example (z : (actualUnshiftedSourceModule mixedDatum mixedScalars (fun _ => 4)
    oddColour.1 [false, true]).obj (⟨[true, false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) :
    OldInductionRepresentable.upperHomEquiv mixedDatum mixedScalars (fun _ => 4) oddColour.1
      (⟨[false, true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
      (⟨[true, false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
      (((oldModuleMate mixedDatum mixedScalars (fun _ => 4) oddColour.1).app 1
        (oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩)).total
        (⟨[true, false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) z) =
    -toCyclotomic mixedDatum mixedScalars (fun _ => 4) oddColour.1 [false, true] [true, false]
      (shiftedSourceCanonicalEquiv mixedDatum mixedScalars (fun _ => 4)
        oddColour [false, true] [true, false] z) :=
  oldModuleMate_firstRow mixedDatum mixedScalars (fun _ => 4) oddColour [false, true] [true, false] z

example (g : Old mixedDatum mixedScalars (fun _ => 4) ([false] ++ [oddColour.1]) [true, false])
    (b : Old mixedDatum mixedScalars (fun _ => 4) [false, true] ([false] ++ [oddColour.1])) :
    shiftedSourceCanonicalEquiv mixedDatum mixedScalars (fun _ => 4)
      oddColour [false, true] [true, false]
      (BalancedInduction.tensor (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)
        ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj
          (oldRepresentable mixedDatum mixedScalars (fun _ => 4) ⟨[false, true]⟩)).toFunctor
        (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) g b) =
    tensor mixedDatum mixedScalars (fun _ => 4) oddColour.1 [false, true] [false] [true, false]
      (oldTwist mixedDatum mixedScalars (fun _ => 4) 1 ([false] ++ [oddColour.1]) [true, false] g) b :=
  shiftedSourceCanonicalEquiv_tensor mixedDatum mixedScalars (fun _ => 4)
    oddColour [false, true] [false] [true, false] g b

end OldMateFirstRowConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldMateFirstRow
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

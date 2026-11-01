import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputOperators
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenInputOperatorsConsumer
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

open CyclotomicCrossingTensor

example (z : ShortTarget mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true]) :
    evenInputContraction mixedDatum mixedScalars (fun _ => 4) false rfl [true, false] [false, true]
      (q mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true] z) =
    evenInputContractionAffine mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true] z :=
  evenInputContraction_q mixedDatum mixedScalars (fun _ => 4) false rfl [true, false] [false, true] z

example (z : ShortTarget mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true]) :
    evenCrossingInputDot mixedDatum mixedScalars (fun _ => 4) false rfl [true, false] [false, true]
      (q mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true] z) =
    q mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true]
      (evenCrossingInputDotAffine mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true] z) :=
  evenCrossingInputDot_q mixedDatum mixedScalars (fun _ => 4) false rfl [true, false] [false, true] z

example (r : hom mixedDatum mixedScalars (fun _ => 4) [true, false] ([true] ++ [false]))
    (g : hom mixedDatum mixedScalars (fun _ => 4) ([true] ++ [false]) [false, true]) :
    evenInputContraction mixedDatum mixedScalars (fun _ => 4) false rfl [true, false] [false, true]
      (q mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true]
        (shortTensor mixedDatum mixedScalars (fun _ => 4) false [true, false] [true] [false, true] g
          ((ideal mixedDatum mixedScalars (fun _ => 4) [true, false] ([true] ++ [false])).mkQ r))) =
    -(ideal mixedDatum mixedScalars (fun _ => 4) [true, false] [false, true]).mkQ (r ≫ g) :=
  evenInputContraction_representative mixedDatum mixedScalars (fun _ => 4)
    false rfl [true, false] [true] [false, true] r g

example (r : hom mixedDatum mixedScalars (fun _ => 4) [true, false] ([true] ++ [false]))
    (g : hom mixedDatum mixedScalars (fun _ => 4) ([true] ++ [false]) [false, true]) :
    evenCrossingInputDotAffine mixedDatum mixedScalars (fun _ => 4) false [true, false] [false, true]
      (shortTensor mixedDatum mixedScalars (fun _ => 4) false [true, false] [true] [false, true] g
        ((ideal mixedDatum mixedScalars (fun _ => 4) [true, false] ([true] ++ [false])).mkQ r)) =
    shortTensor mixedDatum mixedScalars (fun _ => 4) false [true, false] [true] [false, true]
      (appendMovingPower mixedDatum mixedScalars (fun _ => 4) false [true] 1 ≫ g)
      ((ideal mixedDatum mixedScalars (fun _ => 4) [true, false] ([true] ++ [false])).mkQ r) :=
  evenCrossingInputDotAffine_representative mixedDatum mixedScalars (fun _ => 4)
    false rfl [true, false] [true] [false, true] r g
end EvenInputOperatorsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputOperators
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

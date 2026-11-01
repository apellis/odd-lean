import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ShiftedMatrixFamiliesConsumer
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



private abbrev C := OldCategory mixedDatum mixedScalars (fun _ => 4)
private abbrev H : Superfunctor ℚ C (SVec ℚ) :=
  oldRepresentable mixedDatum mixedScalars (fun _ => 4) (⟨[false, true]⟩ : C)
local instance : PiSupercategory ℚ (Superfunctor ℚ C (SVec ℚ)) := supermodulePiSupercategory

example (i : Bool) (a : Option (Fin 3)) :
    unitMatrixEntry mixedDatum mixedScalars (fun _ => 4) i H 3 a ∈ parity (R := ℚ) _ _ 0 :=
  unitMatrixEntry_mem mixedDatum mixedScalars (fun _ => 4) i H 3 a

example (i : Bool) (a : Option (Fin 3)) :
    capMatrixEntry mixedDatum mixedScalars (fun _ => 4) i H 3 a ∈ parity (R := ℚ) _ _ 0 :=
  capMatrixEntry_mem mixedDatum mixedScalars (fun _ => 4) i H 3 a

example (i : Bool) (n : ℕ) :
    SVec.toLinearMap (((inductionDotModule mixedDatum mixedScalars (fun _ => 4) i H) ^ n).total
      (⟨[true, false]⟩ : C)) =
      (actualInductionDot mixedDatum mixedScalars (fun _ => 4) i H (⟨[true, false]⟩ : C)) ^ n :=
  inductionDotModule_power_total mixedDatum mixedScalars (fun _ => 4) i H ⟨[true, false]⟩ n

example (r : Fin 3) : unitMatrixFamily mixedDatum mixedScalars (fun _ => 4) true H 3 (some r) =
    (SKM.homParityShift (k := ℚ) (r.val • (1 : ZMod 2))).obj H := rfl

example (r : Fin 3) : capMatrixFamily mixedDatum mixedScalars (fun _ => 4) true H 3 (some r) =
    (SKM.homParityShift (k := ℚ) (r.val • (1 : ZMod 2))).obj H := rfl

example : unitMatrixFamily mixedDatum mixedScalars (fun _ => 4) true H 0 none =
    supermoduleParityObj
      ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) true)).obj
        ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) true)).obj H)) := rfl

example : capMatrixFamily mixedDatum mixedScalars (fun _ => 4) false H 0 none =
    (BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) false)).obj
      ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) false)).obj H) := rfl

example (i : Bool) : unitMatrixEntry mixedDatum mixedScalars (fun _ => 4) i H 0 none ∈
    parity (R := ℚ) _ _ 0 := unitMatrixEntry_mem mixedDatum mixedScalars (fun _ => 4) i H 0 none
end ShiftedMatrixFamiliesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

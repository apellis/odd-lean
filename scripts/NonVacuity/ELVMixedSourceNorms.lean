import OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceNorms
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import StringDiagrams.Super.PiTwo
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVMixedSourceNorms

local instance homPi {A B : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { CyclotomicAction.AsymmetricParameters.datum with
    parity := fun _ => 0
    even_of_odd := by intro i j hi; norm_num at hi }

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

private theorem step : (0 : Bool → ℤ) + D.α false = D.α false := zero_add _
private abbrev A := elvWeightSpace D Sc (fun _ => 12) 12 (0 : Bool → ℤ) (D.α false)
private def E : A ⟶ A := 𝟙 A
private def H : A ⟶ A := 𝟙 A


/-- Closed actual module-category source with the prescribed identity probe dot. -/
example :=
  elvMixedSource_difference_isUnit D Sc (fun _ => 12) 12 false 0 step E 1 H
    sy hc rfl 1 (id_mem E) isUnit_one

example : elvPostTransposeDot D Sc (fun _ => 12) 12 false 0 step
      (E ≫ (SKM.homParityShift (k := ℚ) 1).obj H) =
    SKM.mixedPostSourcePostDot (k := ℚ) E 1 H
      (elvActionAdjunction D Sc (fun _ => 12) 12 false 0 step)
      (elvActionDot D Sc (fun _ => 12) 12 false 0 step) :=
  elvMixedSourceTransposeDot_eq D Sc (fun _ => 12) 12 false 0 step E 1 H

end NonVacuity.ELVMixedSourceNorms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceNorms
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

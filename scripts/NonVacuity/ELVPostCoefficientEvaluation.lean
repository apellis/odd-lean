import OddMath.QuiverHecke.CyclotomicAction.ELVPostCoefficientEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.PostCoefficientEvaluationExamples
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
private abbrev A := elvWeightSpace D Sc (fun _ => 12) 12 (0 : Bool → ℤ) 0
private abbrev F : A ⟶ A := 𝟙 A


private abbrev G := elvPostInduction D Sc (fun _ => 12) 12 false 0 step F
private abbrev Y : End G := elvPostDot D Sc (fun _ => 12) 12 false 0 step F
private def vacuumBlock : WeightBlocks D (0 : Bool → ℤ) 0 :=
  ⟨0, by simp [blockWeight]⟩
private def sourceVacuum : ELVWeightProduct D Sc (fun _ => 12) 12 (0 : Bool → ℤ) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D Sc (fun _ => 12) 12)
  else elvZeroModule D Sc (fun _ => 12) 12 β.1
private abbrev δ := blockSucc D 0 false step vacuumBlock
private abbrev φ := elvPostEndEvaluation D Sc (fun _ => 12) 12 false 0 step F sourceVacuum δ
private theorem denominatorUnit : IsUnit (Y - 1) := by
  apply elvPostDot_difference_isUnit D Sc (fun _ => 12) 12 sy hc false 0 step F rfl
    1 (id_mem G) isUnit_one
  intro M ε
  change Commute (show End ((G.obj M) ε) from _) (1 : End ((G.obj M) ε))
  exact Commute.one_right _
example : IsNilpotent (φ Y) :=
  elvPostEndEvaluation_dot_isNilpotent D Sc (fun _ => 12) 12 false 0 step F sy hc sourceVacuum δ
example : φ Y = Y.app 0 sourceVacuum δ :=
  elvPostEndEvaluation_of_mem D Sc (fun _ => 12) 12 false 0 step F sourceVacuum δ Y
    (elvPostDot_mem D Sc (fun _ => 12) 12 false 0 step F)
example : ∃ n : ℕ, φ Y ^ n = 0 ∧
    φ (Ring.inverse (Y - 1)) = -∑ r ∈ Finset.range n, Ring.inverse (φ 1) ^ (r+1) * φ Y ^ r :=
  elvPostCoefficient_even_expansion D Sc (fun _ => 12) 12 false 0 step F sy hc
    1 (Ring.inverse (Y - 1)) isUnit_one (Commute.one_left Y)
    (Ring.inverse_mul_cancel _ denominatorUnit) sourceVacuum δ

-- The same constructed bound also applies to an occupied odd output.
private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private theorem stepo : (0 : Bool → ℤ) + Do.α false = Do.α false := zero_add _
private abbrev Fo := Superfunctor.id ℚ (ELVWeightProduct Do So (fun _ => 12) 12 (0 : Bool → ℤ) 0)
private def vacuumBlocko : WeightBlocks Do (0 : Bool → ℤ) 0 :=
  ⟨0, by simp [blockWeight]⟩
private def sourceVacuumo : ELVWeightProduct Do So (fun _ => 12) 12 (0 : Bool → ℤ) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule Do So (fun _ => 12) 12)
  else elvZeroModule Do So (fun _ => 12) 12 β.1
example : IsNilpotent
    (elvPostEndEvaluation Do So (fun _ => 12) 12 false 0 stepo Fo sourceVacuumo
      (blockSucc Do 0 false stepo vacuumBlocko)
      (elvPostDot Do So (fun _ => 12) 12 false 0 stepo Fo)) :=
  elvPostEndEvaluation_dot_isNilpotent Do So (fun _ => 12) 12 false 0 stepo Fo
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous _ _
end OddMath.QuiverHecke.PostCoefficientEvaluationExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPostCoefficientEvaluation
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ShiftedCoefficientEvaluationExamples
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
private abbrev Gs (κ : ZMod 2) := elvShiftedPostInduction D Sc (fun _ => 12) 12 false 0 step F κ
private abbrev Ys (κ : ZMod 2) : End (Gs κ) := elvShiftedPostDot D Sc (fun _ => 12) 12 false 0 step F κ
private abbrev Xs (κ : ZMod 2) : End (Gs κ) :=
  elvShiftedPostEnd D Sc (fun _ => 12) 12 false 0 step F
    (elvPostProbeDot D Sc (fun _ => 12) 12 false 0 step F 1) κ
private abbrev φ (κ : ZMod 2) :=
  elvShiftedPostEndEvaluation D Sc (fun _ => 12) 12 false 0 step F κ sourceVacuum δ
private theorem denominatorUnit (κ : ZMod 2) : IsUnit (Ys κ - Xs κ) :=
  elvShiftedPostProbe_difference_isUnit D Sc (fun _ => 12) 12 false 0 step F sy hc κ rfl
    1 (id_mem F) isUnit_one
example (κ : ZMod 2) : IsNilpotent (φ κ (Ys κ)) :=
  elvShiftedPostEndEvaluation_dot_isNilpotent D Sc (fun _ => 12) 12 false 0 step F sy hc κ sourceVacuum δ
example (κ : ZMod 2) : IsUnit (φ κ (Xs κ)) :=
  elvShiftedPostEndEvaluation_probe_isUnit D Sc (fun _ => 12) 12 false 0 step F 1 isUnit_one κ sourceVacuum δ

/-- This is the evaluated inverse of the actual shifted difference, not a supplied coefficient equation. -/
example (κ : ZMod 2) : ∃ n : ℕ, φ κ (Ys κ) ^ n = 0 ∧
    φ κ (Ring.inverse (Ys κ - Xs κ)) =
      -∑ r ∈ Finset.range n, Ring.inverse (φ κ (Xs κ)) ^ (r + 1) * φ κ (Ys κ) ^ r :=
  elvShiftedPostCoefficient_even_expansion D Sc (fun _ => 12) 12 false 0 step F sy hc rfl
    1 (id_mem F) isUnit_one κ (Ring.inverse (Ys κ - Xs κ))
    (Ring.inverse_mul_cancel _ (denominatorUnit κ)) sourceVacuum δ

-- The same constructed bound also applies to an occupied odd output.
private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private theorem stepo : (0 : Bool → ℤ) + Do.α false = Do.α false := zero_add _
private abbrev Ao := elvWeightSpace Do So (fun _ => 12) 12 (0 : Bool → ℤ) 0
private abbrev Fo : Ao ⟶ Ao := 𝟙 Ao
private def vacuumBlocko : WeightBlocks Do (0 : Bool → ℤ) 0 :=
  ⟨0, by simp [blockWeight]⟩
private def sourceVacuumo : ELVWeightProduct Do So (fun _ => 12) 12 (0 : Bool → ℤ) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule Do So (fun _ => 12) 12)
  else elvZeroModule Do So (fun _ => 12) 12 β.1
-- The genuine odd postdot is evaluated after either prescribed content shift.
example (κ : ZMod 2) : IsNilpotent
    (elvShiftedPostEndEvaluation Do So (fun _ => 12) 12 false 0 stepo Fo κ sourceVacuumo
      (blockSucc Do 0 false stepo vacuumBlocko)
      (elvShiftedPostDot Do So (fun _ => 12) 12 false 0 stepo Fo κ)) :=
  elvShiftedPostEndEvaluation_dot_isNilpotent Do So (fun _ => 12) 12 false 0 stepo Fo
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous κ _ _

end OddMath.QuiverHecke.ShiftedCoefficientEvaluationExamples
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

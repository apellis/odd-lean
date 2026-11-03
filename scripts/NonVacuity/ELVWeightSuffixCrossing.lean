import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuffixCrossing
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightSuffixExamples
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private abbrev X := Bool → ℤ
private def vacuumBlock : WeightBlocks D (0 : X) 0 := ⟨0, by simp⟩
private theorem step (i : Bool) : (0 : X) + D.α i = D.α i := zero_add _
private theorem step₂ (i j : Bool) : D.α j + D.α i = D.α j + D.α i := rfl
private theorem step₃ (i j l : Bool) : (D.α l + D.α j) + D.α i = (D.α l + D.α j) + D.α i := rfl
private def sourceVacuum : ELVWeightProduct D (parameterTwist D Sc) (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D (parameterTwist D Sc) (fun _ => 12) 12)
  else elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1

private abbrev firstBlock (l : Bool) := blockSucc D (0 : X) l (step l) vacuumBlock
private abbrev pairBlock (j l : Bool) := blockSucc₂ D j l (0 : X) (step l) (step₂ j l) vacuumBlock
private abbrev tripleBlock (i j l : Bool) := elvBlockSucc₃ D i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock
private abbrev hc₁ (l : Bool) := elvBlockSucc_content_eq D l (0 : X) (step l) vacuumBlock
private abbrev hc₂ (j l : Bool) := elvBlockSucc_content_eq D j (0 : X) (step₂ j l) (firstBlock l)
private abbrev hc₃ (i j l : Bool) := elvBlockSucc_content_eq D i (0 : X) (step₃ i j l) (pairBlock j l)
private abbrev hP (j l : Bool) := elvBlockPair_content_eq D j l (0 : X) (step l) (step₂ j l) vacuumBlock
private abbrev hQ (i j l : Bool) := elvBlockPair_content_eq D i j (0 : X) (step₂ j l) (step₃ i j l) (firstBlock l)
private abbrev hT (i j l : Bool) := elvBlockTriple_content_eq D i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock

private theorem swappedLastStep (i j l : Bool) :
    (D.α l + D.α i) + D.α j = (D.α l + D.α j) + D.α i := by abel
private theorem swappedLastPair (i j l : Bool) :
    blockSucc₂ D j i (0 : X) (step₂ i l) (swappedLastStep i j l) (firstBlock l) =
      tripleBlock i j l :=
  blockSucc₂_swap D i j (0 : X) (step₂ j l) (step₃ i j l) (step₂ i l) (swappedLastStep i j l) rfl

/-- The given last-pair crossing retains both actual weight paths. -/
example (i j l : Bool) := elvWeightSuffixCross_total D (parameterTwist D Sc) (fun _ => 12) 12
  i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) (step₂ i l) (swappedLastStep i j l)
  sourceVacuum (tripleBlock i j l)
example (i j l : Bool) := elvWeightSuffixCross_lastBlock D (parameterTwist D Sc) (fun _ => 12) 12
  i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) (step₂ i l) (swappedLastStep i j l)
  vacuumBlock (tripleBlock i j l) rfl sourceVacuum
end OddMath.QuiverHecke.ELVWeightSuffixExamples

namespace OddMath.QuiverHecke.ELVWeightSuffixOddExamples
open CyclotomicAction.AsymmetricParameters
private def vacuumBlock : WeightBlocks datum (0 : Bool → ℤ) 0 := ⟨0, by simp⟩
private def sourceVacuum : ELVWeightProduct datum (parameterTwist datum scalars) (fun _ => 12) 12
    (0 : Bool → ℤ) 0 := fun β => if hb : β.1 = 0 then
      (by rw [hb]; exact vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    else elvZeroModule datum (parameterTwist datum scalars) (fun _ => 12) 12 β.1
private theorem lastSwap (i j l : Bool) :
    (datum.α l + datum.α i) + datum.α j = (datum.α l + datum.α j) + datum.α i := by abel
/-- Distinct odd colours in the last pair, with the actual first-induced input. -/
example := elvWeightSuffixCross_lastBlock datum (parameterTwist datum scalars) (fun _ => 12) 12
  true false true (0 : Bool → ℤ) (zero_add _) rfl rfl rfl (lastSwap true false true)
  vacuumBlock
  (elvBlockSucc₃ datum true false true (0 : Bool → ℤ) (zero_add _) rfl rfl vacuumBlock)
  rfl sourceVacuum
end OddMath.QuiverHecke.ELVWeightSuffixOddExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuffixCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

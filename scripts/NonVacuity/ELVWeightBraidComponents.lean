import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidComponents
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightBraidComponentExamples
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

private abbrev upperTriple (i : Bool) :=
  elvBlockSucc₃ D i i i (0 : X) (step i) (step₂ i i) (step₃ i i i) vacuumBlock

/-- The exact reassociated first crossing, for both moving parities. -/
example (i : Bool) := elvWeightBraidPrefix_total D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (step i) (step₂ i i) (step₃ i i i) sourceVacuum (upperTriple i)
/-- The exact second crossing, on the actual first-induced product module. -/
example (i : Bool) := elvWeightBraidSuffix_total D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (step i) (step₂ i i) (step₃ i i i) sourceVacuum (upperTriple i)

/-- Arbitrary output sectors require no support premise. -/
example (i : Bool) (ε : WeightBlocks D (0 : X) ((D.α i + D.α i) + D.α i)) :=
  elvWeightBraidPrefix_total D (parameterTwist D Sc) (fun _ => 12) 12
    i (0 : X) (step i) (step₂ i i) (step₃ i i i) sourceVacuum ε
example (i : Bool) (ε : WeightBlocks D (0 : X) ((D.α i + D.α i) + D.α i)) :=
  elvWeightBraidSuffix_total D (parameterTwist D Sc) (fun _ => 12) 12
    i (0 : X) (step i) (step₂ i i) (step₃ i i i) sourceVacuum ε

example (i : Bool) := elvWeightBraidPrefix_blockSucc D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (step i) (step₂ i i) (step₃ i i i) vacuumBlock sourceVacuum
example (i : Bool) := elvWeightBraidSuffix_blockSucc D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (step i) (step₂ i i) (step₃ i i i) vacuumBlock sourceVacuum

private theorem missing₁ (i : Bool) : -(D.α i + D.α i + D.α i) + D.α i = -(D.α i + D.α i) := by abel
private theorem missing₂ (i : Bool) : -(D.α i + D.α i) + D.α i = -D.α i := by abel
private theorem missing₃ (i : Bool) : -D.α i + D.α i = (0 : X) := neg_add_cancel _
private theorem vacuumMissing (i : Bool) : ¬ ∃ β,
    elvBlockSucc₃ D i i i (0 : X) (missing₁ i) (missing₂ i) (missing₃ i) β = vacuumBlock := by
  intro ⟨β,hβ⟩
  have hm : i ∈ vacuumBlock.1 :=
    (exists_blockSucc_iff D (0 : X) i (missing₃ i) vacuumBlock).mp
      ⟨blockSucc₂ D i i (0 : X) (missing₁ i) (missing₂ i) β,hβ⟩
  simp [vacuumBlock] at hm
/-- Actual absent triple predecessors, with the same given crossing fields. -/
example (i : Bool) := elvWeightBraidPrefix_total D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (missing₁ i) (missing₂ i) (missing₃ i)
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) vacuumBlock
example (i : Bool) := elvWeightBraidSuffix_total D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (missing₁ i) (missing₂ i) (missing₃ i)
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) vacuumBlock
example (i : Bool) := elvEFunctor_comp₃_isZero D (parameterTwist D Sc) (fun _ => 12) 12
  i i i (0 : X) (missing₁ i) (missing₂ i) (missing₃ i) vacuumBlock (vacuumMissing i)
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1)

end OddMath.QuiverHecke.ELVWeightBraidComponentExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidComponents
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

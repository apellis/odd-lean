import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleInduction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightTripleExamples
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

/-- Every ordered triple includes the repeated even and repeated odd cases. -/
example (i j l : Bool) := elvBlockSucc₃_injective D i j l (0 : X) (step l) (step₂ j l) (step₃ i j l)
example (i j l : Bool) := elvBlockTriple_content_eq D i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock
example (i j l : Bool) := elvBlockTripleInd_content_eq D (parameterTwist D Sc) (fun _ => 12) 12
  i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock
example (i j l : Bool) := Functor.congr_obj
  (elvEFunctor_comp₃_blockSucc D (parameterTwist D Sc) (fun _ => 12) 12
    i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock) sourceVacuum
example (i j l : Bool) := Functor.congr_obj
  (elvEFunctor_comp₃_contentTriple_eq D (parameterTwist D Sc) (fun _ => 12) 12
    i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock _ rfl) sourceVacuum
example (i j l : Bool) := elvWeightTripleComparison_mem D (parameterTwist D Sc) (fun _ => 12) 12
  i j l (0 : X) (step l) (step₂ j l) (step₃ i j l) vacuumBlock _ rfl sourceVacuum

private theorem innerStep : -D.α false + D.α false = (0 : X) := neg_add_cancel _
private abbrev twoTrue := blockSucc₂ D true true (0 : X) (step true) (step₂ true true) vacuumBlock
private theorem innerMissing : ¬ ∃ β,
    elvBlockSucc₃ D true true false (0 : X) innerStep (step true) (step₂ true true) β = twoTrue := by
  intro ⟨β,hβ⟩
  have hp := blockSucc_injective D (0 : X) true (step₂ true true) hβ
  have he := blockSucc_injective D (0 : X) true (step true) hp
  have hm : false ∈ vacuumBlock.1 :=
    (exists_blockSucc_iff D (0 : X) false innerStep vacuumBlock).mp ⟨β,he⟩
  simp [vacuumBlock] at hm
/-- The two outer predecessors exist, but the first predecessor does not. -/
example := elvEFunctor_comp₃_isZero D (parameterTwist D Sc) (fun _ => 12) 12
  true true false (0 : X) innerStep (step true) (step₂ true true) twoTrue innerMissing
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1)

private theorem outerStep : -D.α true + D.α true = (0 : X) := neg_add_cancel _
private theorem beforeOuter : -(D.α true + D.α false) + D.α false = -D.α true := by abel
private theorem earliest : -(D.α true + D.α false + D.α true) + D.α true = -(D.α true + D.α false) := by abel
private theorem outerMissing : ¬ ∃ β,
    elvBlockSucc₃ D true false true (0 : X) earliest beforeOuter outerStep β = vacuumBlock := by
  intro ⟨β,hβ⟩
  have hm : true ∈ vacuumBlock.1 :=
    (exists_blockSucc_iff D (0 : X) true outerStep vacuumBlock).mp
      ⟨blockSucc₂ D false true (0 : X) earliest beforeOuter β,hβ⟩
  simp [vacuumBlock] at hm
example := elvEFunctor_comp₃_isZero D (parameterTwist D Sc) (fun _ => 12) 12
  true false true (0 : X) earliest beforeOuter outerStep vacuumBlock outerMissing
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1)
end OddMath.QuiverHecke.ELVWeightTripleExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleInduction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

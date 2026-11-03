import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedRelation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightMixedRelationExamples
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

/-- The corrected relation for the given natural maps, with both
outer parity choices and every weight equality proved. -/
example := elvRouquierData_braidEq D Sc (fun _ => 12) 12
  false true (0 : X) (step false) (step true) rfl rfl (add_comm _ _) rfl
  (by simp only [add_comm, add_left_comm]) (by decide)
example := elvRouquierData_braidEq D Sc (fun _ => 12) 12
  true false (0 : X) (step true) (step false) rfl rfl (add_comm _ _) rfl
  (by simp only [add_comm, add_left_comm]) (by decide)
private abbrev tripleBlock := elvBlockSucc₃ D false true false (0 : X) (step false) rfl rfl vacuumBlock
private def wordOutput : ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12 tripleBlock.1 :=
  ⟨⟨[false,true,false]⟩, by rfl⟩
/-- The exact field on an occupied coefficient regular-vacuum output. -/
example := by
  have h := elvRouquierData_braidEq D Sc (fun _ => 12) 12
    false true (0 : X) (step false) (step true) rfl rfl (add_comm _ _) rfl
    (by simp only [add_comm, add_left_comm]) (by decide)
  dsimp only [rouquierMixedBraidEquation] at h
  exact congrArg
    (fun f : End (elvE D (parameterTwist D Sc) (fun _ => 12) 12 false (0 : X) (step false) ≫
        elvE D (parameterTwist D Sc) (fun _ => 12) 12 true (0 : X) (step₂ true false) ≫
        elvE D (parameterTwist D Sc) (fun _ => 12) 12 false (0 : X) (step₃ false true false)) =>
      (f.total sourceVacuum tripleBlock).total wordOutput) h

end OddMath.QuiverHecke.ELVWeightMixedRelationExamples

namespace OddMath.QuiverHecke.ELVWeightMixedRelationOddExamples
open CyclotomicAction.AsymmetricParameters
/-- Distinct odd asymmetric colours retain the original parameters. -/
example := elvRouquierData_braidEq datum scalars (fun _ => 12) 12 true false (0 : Bool → ℤ)
  (zero_add _) (zero_add _) rfl rfl (add_comm _ _) rfl
  (by simp only [add_comm, add_left_comm]) (by decide)
end OddMath.QuiverHecke.ELVWeightMixedRelationOddExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedRelation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

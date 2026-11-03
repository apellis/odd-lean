import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedModulePolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightMixedModulePolynomialExamples
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

private def tripleOutput (i j : Bool) :
    ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12
      (elvBlockSucc₃ D i j i (0 : X) (step i) rfl rfl vacuumBlock).1 :=
  ⟨⟨[i,j,i]⟩, by rfl⟩
/-- Occupied outputs with each of the two outer parities. -/
example := elvWeightMixedBraid_module_polynomial D Sc (fun _ => 12) 12
  false true (0 : X) (step false) (step true) rfl rfl (add_comm _ _) rfl
  (by simp only [add_comm, add_left_comm]) vacuumBlock (by decide) sourceVacuum
example := elvWeightMixedBraid_module_polynomial D Sc (fun _ => 12) 12
  true false (0 : X) (step true) (step false) rfl rfl (add_comm _ _) rfl
  (by simp only [add_comm, add_left_comm]) vacuumBlock (by decide) sourceVacuum
end OddMath.QuiverHecke.ELVWeightMixedModulePolynomialExamples
namespace OddMath.QuiverHecke.ELVWeightMixedModulePolynomialOddExamples
open CyclotomicAction.AsymmetricParameters
private def vacuumBlock : WeightBlocks datum (0 : Bool → ℤ) 0 := ⟨0, by simp⟩
private def sourceVacuum : ELVWeightProduct datum (parameterTwist datum scalars) (fun _ => 12) 12
    (0 : Bool → ℤ) 0 := fun β => if hb : β.1 = 0 then
      (by rw [hb]; exact vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    else elvZeroModule datum (parameterTwist datum scalars) (fun _ => 12) 12 β.1
private def tripleOutput : ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
    (elvBlockSucc₃ datum true false true (0 : Bool → ℤ) (zero_add _) rfl rfl vacuumBlock).1 :=
  ⟨⟨[true,false,true]⟩, by rfl⟩
/-- Distinct odd colours in the asymmetric Cartan datum: the given crossing
has odd degree, with a nonreflexive change of the intermediate weight. -/
example := elvWeightMixedBraid_module_polynomial datum scalars (fun _ => 12) 12
  true false (0 : Bool → ℤ) (zero_add _) (zero_add _) rfl rfl (add_comm _ _) rfl
  (by simp only [add_comm, add_left_comm]) vacuumBlock (by decide) sourceVacuum
end OddMath.QuiverHecke.ELVWeightMixedModulePolynomialOddExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedModulePolynomial
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

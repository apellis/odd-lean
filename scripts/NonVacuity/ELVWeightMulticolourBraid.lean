import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightMulticolourBraidExamples
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

/-- Distinct outer colours, with either middle colour. -/
example (j : Bool) := elvActionCross_multicolour_braid D (parameterTwist D Sc) (fun _ => 12) 12
  false j true (0 : X) (step true) (step j) (step false)
  rfl rfl (add_comm _ _) rfl (add_comm _ _) (add_comm _ _)
  rfl (by abel) (by abel) (by simp)
example (j : Bool) := elvActionCross_multicolour_braid D (parameterTwist D Sc) (fun _ => 12) 12
  true j false (0 : X) (step false) (step j) (step true)
  rfl rfl (add_comm _ _) rfl (add_comm _ _) (add_comm _ _)
  rfl (by abel) (by abel) (by simp)
/-- The same-colour case allows each outer parity and retains all paths. -/
example (i : Bool) := elvActionCross_multicolour_braid D (parameterTwist D Sc) (fun _ => 12) 12
  i i i (0 : X) (step i) (step i) (step i)
  rfl rfl (add_comm _ _) rfl (add_comm _ _) (add_comm _ _)
  rfl (by abel) (by abel) (by simp)
end OddMath.QuiverHecke.ELVWeightMulticolourBraidExamples
namespace OddMath.QuiverHecke.ELVWeightMulticolourBraidOddExamples
open CyclotomicAction.AsymmetricParameters
private def vacuumBlock : WeightBlocks datum (0 : Bool → ℤ) 0 := ⟨0, by simp⟩
private def sourceVacuum : ELVWeightProduct datum (parameterTwist datum scalars) (fun _ => 12) 12
    (0 : Bool → ℤ) 0 := fun β => if hb : β.1 = 0 then
      (by rw [hb]; exact vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    else elvZeroModule datum (parameterTwist datum scalars) (fun _ => 12) 12 β.1
/-- Distinct odd outer colours in the asymmetric Cartan datum. -/
example := elvActionCross_multicolour_braid datum (parameterTwist datum scalars) (fun _ => 12) 12
  true false false (0 : Bool → ℤ) (zero_add _) (zero_add _) (zero_add _)
  rfl rfl (add_comm _ _) rfl (add_comm _ _) (add_comm _ _)
  rfl (by abel) (by abel) (by decide)
end OddMath.QuiverHecke.ELVWeightMulticolourBraidOddExamples

namespace OddMath.QuiverHecke.ELVWeightMulticolourBraidThreeColours
open SKM
private def D : Datum (Fin 3) (Fin 3 → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else -2
    coroot := fun i => LinearMap.proj i
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      simp [CartanDatum.cartanMatrix_apply, hij]
    zero_comm := by
      intro i j
      by_cases h : i = j
      · subst j; simp [CartanDatum.cartanMatrix_apply]
      · simp [CartanDatum.cartanMatrix_apply, h, Ne.symm h] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split_ifs <;> norm_num [even_iff_two_dvd]
private def Sc : Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def vacuumBlock : WeightBlocks D (0 : Fin 3 → ℤ) 0 := ⟨0, by simp⟩
private def sourceVacuum : ELVWeightProduct D (parameterTwist D Sc) (fun _ => 12) 12
    (0 : Fin 3 → ℤ) 0 := fun β => if hb : β.1 = 0 then
      (by rw [hb]; exact vacuumModule D (parameterTwist D Sc) (fun _ => 12) 12)
    else elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1
/-- Three distinct odd colours with nonzero pair Cartan entries. Every
intermediate original weight and all six chosen paths are exercised. -/
example := elvActionCross_multicolour_braid D (parameterTwist D Sc) (fun _ => 12) 12
  (0 : Fin 3) 1 2 (0 : Fin 3 → ℤ) (zero_add _) (zero_add _) (zero_add _)
  rfl rfl (add_comm _ _) rfl (add_comm _ _) (add_comm _ _)
  rfl (by abel) (by abel) (by decide)
end OddMath.QuiverHecke.ELVWeightMulticolourBraidThreeColours

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMulticolourBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

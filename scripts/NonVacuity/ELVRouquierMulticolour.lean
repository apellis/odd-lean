import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVRouquierMulticolourExamples
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
private def highest : X := fun _ => 4
private theorem cutoff_pairing : ∀ i, ((4 : ℕ) : ℤ) = D.h i highest := by
  intro i
  rfl
/-- A mixed even/odd full original-parameter action family, with positive
cutoff and the exact highest-weight pairing supplied. -/
example : SKM.RouquierMulticolour
    (elvRouquierFamily D (parameterTwist D Sc) (fun _ => 4) 12 highest cutoff_pairing) Sc :=
  elvRouquierMulticolour D Sc (fun _ => 4) 12 highest cutoff_pairing

private def vacuumBlock : WeightBlocks D highest (-highest) := ⟨0, by simp [blockWeight]⟩
private def regularInput : ELVWeightProduct D (parameterTwist D Sc) (fun _ => 4) 12
    highest (-highest) := fun β => if hb : β.1 = 0 then
      (by rw [hb]; exact vacuumModule D (parameterTwist D Sc) (fun _ => 4) 12)
    else elvZeroModule D (parameterTwist D Sc) (fun _ => 4) 12 β.1
/-- The full record exposes its actual distinct inverse, with all four
weight corners fixed at the occupied lowest sector and its successors. -/
example := (elvRouquierMulticolour D Sc (fun _ => 4) 12 highest cutoff_pairing).invNe
  false true (by decide) (x := -highest)
  rfl rfl rfl (by abel)
end OddMath.QuiverHecke.ELVRouquierMulticolourExamples

namespace OddMath.QuiverHecke.ELVRouquierMulticolourOddExamples
open CyclotomicAction.AsymmetricParameters
private def highest : Bool → ℤ := fun _ => 4
private theorem cutoff_pairing : ∀ i, ((4 : ℕ) : ℤ) = datum.h i highest := by
  intro i
  rfl
/-- Both vertices odd and asymmetric Cartan exponents, at a nonzero
highest weight. No local matrix inverse is assumed by the constructor. -/
example : SKM.RouquierMulticolour
    (elvRouquierFamily datum (parameterTwist datum scalars) (fun _ => 4) 12 highest cutoff_pairing) scalars :=
  elvRouquierMulticolour datum scalars (fun _ => 4) 12 highest cutoff_pairing
end OddMath.QuiverHecke.ELVRouquierMulticolourOddExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

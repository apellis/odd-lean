import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDistinctSlideRelations
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVWeightDistinctSlideRelations
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if (p : ZMod 2) * D.parity i = 0 ∧
    (q : ZMod 2) * D.parity j = 0 then 1 else 0
  s_symm := by intro i j p q; simp only [and_comm]
  s_eq_zero := by intro i j p q h; simp [h]
  two_isUnit := by intro _; norm_num
private abbrev X := Bool → ℤ
private theorem step (i : Bool) : (0 : X) + D.α i = D.α i := zero_add _
private theorem step₂ (i j : Bool) : D.α j + D.α i = D.α j + D.α i := rfl
private theorem step₄ (i j : Bool) : D.α i + D.α j = D.α j + D.α i := add_comm _ _

example := elvActionCross_slideLeft_distinct D (parameterTwist D Sc) (fun _ => 12) 12
  true false (0 : X) (step false) (step₂ true false) (step true) (step₄ true false) (by decide)
example := elvActionCross_slideLeft_distinct D (parameterTwist D Sc) (fun _ => 12) 12
  false true (0 : X) (step true) (step₂ false true) (step false) (step₄ false true) (by decide)
example := elvActionCross_slideRight_distinct D (parameterTwist D Sc) (fun _ => 12) 12
  true false (0 : X) (step false) (step₂ true false) (step true) (step₄ true false) (by decide)
example := elvActionCross_slideRight_distinct D (parameterTwist D Sc) (fun _ => 12) 12
  false true (0 : X) (step true) (step₂ false true) (step false) (step₄ false true) (by decide)
private def vacuumBlock : WeightBlocks D (0 : X) 0 := ⟨0, by simp⟩
private def oneBlock := blockSucc D (0 : X) true (step true) vacuumBlock
private def missingWord : ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12 oneBlock.1 where
  obj := ⟨[true]⟩
  content := by change ([true] : Multiset Bool) = ([true] : Multiset Bool) + 0; rw [add_zero]
private theorem h₁ : (-D.α false) + D.α false = (0 : X) := neg_add_cancel _
private theorem h₂ : (0 : X) + D.α true = D.α true := zero_add _
private theorem h₃ : (-D.α false) + D.α true = D.α true - D.α false := by abel
private theorem h₄ : (D.α true - D.α false) + D.α false = D.α true := by abel
example := elvWeightDistinct_slideLeft_component D (parameterTwist D Sc) (fun _ => 12) 12
  true false (0 : X) h₁ h₂ h₃ h₄ (by decide)
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) oneBlock missingWord
example := elvWeightDistinct_slideRight_component D (parameterTwist D Sc) (fun _ => 12) 12
  true false (0 : X) h₁ h₂ h₃ h₄ (by decide)
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) oneBlock missingWord
example := elvActionCross_slideLeft_distinct AsymmetricParameters.datum AsymmetricParameters.scalars
  (fun _ => 12) 12 true false (0 : X) (zero_add _) rfl (zero_add _) (add_comm _ _) (by decide)
example := elvActionCross_slideRight_distinct AsymmetricParameters.datum AsymmetricParameters.scalars
  (fun _ => 12) 12 false true (0 : X) (zero_add _) rfl (zero_add _) (add_comm _ _) (by decide)
end NonVacuity.ELVWeightDistinctSlideRelations

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctSlides,
      `OddMath.QuiverHecke.CyclotomicAction.ELVWeightDistinctSlides,
      `OddMath.QuiverHecke.CyclotomicAction.ELVWeightDistinctSlideRelations] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"

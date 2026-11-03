import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNilHeckeRelation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVWeightNilHeckeRelation
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
private theorem step₄ (i j : Bool) : D.α i + D.α j = D.α j + D.α i := add_comm _ _

private def sourceVacuum : ELVWeightProduct D (parameterTwist D Sc) (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D (parameterTwist D Sc) (fun _ => 12) 12)
  else elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1

private def outputWord (i j : Bool) : ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12
    (blockSucc₂ D i j (0 : X) (step j) (step₂ i j) vacuumBlock).1 where
  obj := ⟨[j,i]⟩
  content := by
    change ([j,i] : Multiset Bool) = ([i] : Multiset Bool) + (([j] : Multiset Bool) + 0)
    rw [add_zero]
    change ([j] : Multiset Bool) + ([i] : Multiset Bool) = ([i] : Multiset Bool) + ([j] : Multiset Bool)
    exact add_comm _ _


example (i : Bool) := elvActionCross_slideLeft D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (step i) (step₂ i i)
example (i : Bool) := elvActionCross_slideRight D (parameterTwist D Sc) (fun _ => 12) 12
  i (0 : X) (step i) (step₂ i i)
example (i : Bool) := elvWeightCrossComponent_slideLeft
  D (parameterTwist D Sc) (fun _ => 12) 12 i (0 : X) (step i) (step₂ i i)
  sourceVacuum (blockSucc₂ D i i (0 : X) (step i) (step₂ i i) vacuumBlock) (outputWord i i)
example (i : Bool) := elvWeightCrossComponent_slideRight
  D (parameterTwist D Sc) (fun _ => 12) 12 i (0 : X) (step i) (step₂ i i)
  sourceVacuum (blockSucc₂ D i i (0 : X) (step i) (step₂ i i) vacuumBlock) (outputWord i i)
private theorem missingFirst :
    (D.α true - D.α false - D.α false) + D.α false = D.α true - D.α false := by abel
private theorem missingSecond : (D.α true - D.α false) + D.α false = D.α true := by abel
private abbrev oneBlock := blockSucc D (0 : X) true (step true) vacuumBlock
private def missingWord : ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12 oneBlock.1 where
  obj := ⟨[true]⟩
  content := by change ([true] : Multiset Bool) = ([true] : Multiset Bool) + 0; rw [add_zero]


example := elvWeightCrossComponent_slideLeft D (parameterTwist D Sc) (fun _ => 12) 12
  false (0 : X) missingFirst missingSecond
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) oneBlock missingWord
example := elvWeightCrossComponent_slideRight D (parameterTwist D Sc) (fun _ => 12) 12
  false (0 : X) missingFirst missingSecond
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) oneBlock missingWord

-- Both nonzero odd degrees occur in the all-odd asymmetric datum.
example := elvActionCross_slideLeft AsymmetricParameters.datum AsymmetricParameters.scalars
  (fun _ => 12) 12 true (0 : X) (zero_add _) rfl
example := elvActionCross_slideRight AsymmetricParameters.datum AsymmetricParameters.scalars
  (fun _ => 12) 12 false (0 : X) (zero_add _) rfl
end NonVacuity.ELVWeightNilHeckeRelation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVWeightNilHecke,
      `OddMath.QuiverHecke.CyclotomicAction.ELVWeightNilHeckeRelation] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"

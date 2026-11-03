import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticComponents
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightQuadraticComponentsExamples

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

/-- Both supported mixed orders use the independent weight dots and
the original parameter polynomial, with no relation premise. -/
example := elvWeightCrossComponent_quadratic_total D Sc (fun _ => 12) 12 true false (0 : X)
  (step false) (step₂ true false) (step true) (step₄ true false) (by decide)
  sourceVacuum _ (outputWord true false)

example := elvWeightCrossComponent_quadratic_total D Sc (fun _ => 12) 12 false true (0 : X)
  (step true) (step₂ false true) (step false) (step₄ false true) (by decide)
  sourceVacuum _ (outputWord false true)

private theorem innerMissingStep : -D.α false + D.α false = (0 : X) := neg_add_cancel _
private theorem outerPresentStep : (0 : X) + D.α true = D.α true := zero_add _
private theorem swappedLastStep : (-D.α false + D.α true) + D.α false = D.α true := by abel
private abbrev oneBlock := blockSucc D (0 : X) true outerPresentStep vacuumBlock
private theorem innerMissing : ¬ ∃ β,
    blockSucc₂ D true false (0 : X) innerMissingStep outerPresentStep β = oneBlock := by
  intro ⟨β, hβ⟩
  have he : blockSucc D (0 : X) false innerMissingStep β = vacuumBlock :=
    blockSucc_injective D (0 : X) true outerPresentStep hβ
  have hm : false ∈ vacuumBlock.1 :=
    (exists_blockSucc_iff D (0 : X) false innerMissingStep vacuumBlock).mp ⟨β, he⟩
  simp [vacuumBlock] at hm

private def missingWord : ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12 oneBlock.1 where
  obj := ⟨[true]⟩
  content := by change ([true] : Multiset Bool) = ([true] : Multiset Bool) + 0; rw [add_zero]

/-- The inner predecessor is absent while the outer predecessor is present;
the global polynomial equality still has no support premise. -/
example := elvWeightCrossComponent_quadratic_total D Sc (fun _ => 12) 12 true false (0 : X)
  innerMissingStep outerPresentStep rfl swappedLastStep (by decide)
  (fun β => elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1) oneBlock missingWord

end OddMath.QuiverHecke.ELVWeightQuadraticComponentsExamples


noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightQuadraticComponentsOddExamples

private def D : SKM.Datum Bool (Bool → ℤ) := AsymmetricParameters.datum
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


/-- Both supported all-odd orders use the independent weight dots and
the original parameter polynomial, with no relation premise. -/
example := elvWeightCrossComponent_quadratic_total D Sc (fun _ => 12) 12 true false (0 : X)
  (step false) (step₂ true false) (step true) (step₄ true false) (by decide)
  sourceVacuum _ (outputWord true false)

example := elvWeightCrossComponent_quadratic_total D Sc (fun _ => 12) 12 false true (0 : X)
  (step true) (step₂ false true) (step false) (step₄ false true) (by decide)
  sourceVacuum _ (outputWord false true)

end OddMath.QuiverHecke.ELVWeightQuadraticComponentsOddExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticComponents
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

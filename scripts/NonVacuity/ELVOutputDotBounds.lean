import OddMath.QuiverHecke.CyclotomicAction.ELVOutputDotBounds
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace OutputDotBoundsConsumer
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def cutoff : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

example (i : Bool) (x : Bool → ℤ) (A : PiSCat.{0,0,1} ℚ)
    (F : A ⟶ elvWeightSpace D Sc cutoff 12 Λ x)
    (δ : WeightBlocks D Λ (x + D.α i)) :=
  elvPostEndEvaluation_dot_pow_zero D Sc cutoff 12 i Λ rfl F sy hc δ

-- The chosen content shift and both moving parities retain one exponent
-- for every module input, at arbitrary fixed output content.
example (i : Bool) (κ : ZMod 2) (x : Bool → ℤ) (A : PiSCat.{0,0,1} ℚ)
    (F : A ⟶ elvWeightSpace D Sc cutoff 12 Λ x)
    (δ : WeightBlocks D Λ (x + D.α i)) :=
  elvShiftedPostEndEvaluation_dot_pow_zero D Sc cutoff 12 i Λ rfl F sy hc κ δ

example (x : Bool → ℤ) (A : PiSCat.{0,0,1} ℚ)
    (F : A ⟶ elvWeightSpace D Sc cutoff 12 Λ x) (f : End F)
    (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : ∀ M : A, End.of (f.total M δ) ^ n = 0) :=
  outputEnd_pow_zero D Sc cutoff 12 Λ x A F f δ n hf

private def m : Bool → ℕ := fun i => if i then 4 else 3
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end OutputDotBoundsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOutputDotBounds
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

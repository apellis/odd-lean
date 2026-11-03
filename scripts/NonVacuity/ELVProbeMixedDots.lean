import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMixedDots
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeMixedDotsConsumer
local instance homPi (A B : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
private abbrev D := WeightedAppendFixture.datum
private abbrev S := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private def cutoff : Bool → ℕ := fun _ => 4
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private def ΛR : Bool → ℤ := fun _ => 4
private def β : Bool →₀ ℕ := Finsupp.single false 1 + Finsupp.single true 1
private theorem step (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private abbrev Hom (i : Bool) :=
  probeOldWeightSpace D (parameterTwist D S) m ΛP
    (-(ΛP - SwappedAssembly.contentWeight D (β + Finsupp.single i 1))) ⟶
  elvWeightSpace D (parameterTwist D S) cutoff 12 ΛR 0
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : S.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

-- Both parities and every whole input Hom, with a nonempty mixed formal probe content.
example (i : Bool) (Z : Hom i) :=
  probeELVMixedPreDot_mem (D := D) (Sc := S) (m := m) (cutoff := cutoff) (bound := 12)
    (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z)
example (i : Bool) (Z : Hom i) :=
  probeELVMixedPreDot_isUnit (D := D) (Sc := S) (m := m) (cutoff := cutoff) (bound := 12)
    (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z)
example (κ : ZMod 2) (Z : Hom false) :=
  probeELVMixed_difference_isUnit (D := D) (Sc := S) (m := m) (cutoff := cutoff) (bound := 12)
    (ΛP := ΛP) (ΛR := ΛR) (i := false) (β := β) (h := step false) (Z := Z) sy hc κ rfl
example (κ : ZMod 2) (Z : Hom true) :=
  probeELVMixed_square_difference_isUnit (D := D) (Sc := S) (m := m) (cutoff := cutoff) (bound := 12)
    (ΛP := ΛP) (ΛR := ΛR) (i := true) (β := β) (h := step true) (Z := Z) sy hc κ rfl

-- The original probe append functors have explicit nonzero vectors at both colours.
example (i : Bool) : probeOldVacuumAppendVector D S m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D S m i (by cases i <;> decide)

private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private def ΛPo : Bool → ℤ := fun i => probeCutoff Do m i
private theorem stepo (i : Bool) : (0 : Bool → ℤ) + Do.α i = Do.α i := zero_add _
private abbrev Homo (i : Bool) :=
  probeOldWeightSpace Do (parameterTwist Do So) m ΛPo
    (-(ΛPo - SwappedAssembly.contentWeight Do (β + Finsupp.single i 1))) ⟶
  elvWeightSpace Do (parameterTwist Do So) cutoff 12 ΛR 0
example (i : Bool) (κ : ZMod 2) (Z : Homo i) :=
  probeELVMixed_square_difference_isUnit (D := Do) (Sc := So) (m := m) (cutoff := cutoff) (bound := 12)
    (ΛP := ΛPo) (ΛR := ΛR) (i := i) (β := β) (h := stepo i) (Z := Z)
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous κ rfl
example (i : Bool) : probeOldVacuumAppendVector Do So m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero Do So m i (by cases i <;> decide)
end ProbeMixedDotsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMixedDots
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

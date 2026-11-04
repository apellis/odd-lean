import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedContentBends
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbePaddedContentBendsConsumer
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private def cutoff : Bool → ℕ := fun _ => 4
private def ΛR : Bool → ℤ := fun _ => 4
private theorem hP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i ΛP := rfl
private theorem hR (i : Bool) : (cutoff i : ℤ) = D.h i ΛR := rfl
private abbrev P := elvProbeReservoir D Sc m cutoff 12 ΛP ΛR hP hR
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

-- Both parities, every sector, and the entire input functor remain present.
example (i : Bool) (t : Sector Bool) (Z : P.H t)
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbe_content_padded_central_separated_windows_above
    D Sc m cutoff 12 ΛP ΛR hP hR i t Z δ sy hc 7

private def corner (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)
example (i : Bool) : StepValid (false, i) true (corner i) ∧
    StepValid (true, i) false (corner i) := by simp [corner, StepValid]
example (i : Bool) (Z : P.H (corner i))
    (δ : WeightBlocks D ΛR (P.muM (corner i))) :=
  elvProbe_content_padded_central_separated_windows_above
    D Sc m cutoff 12 ΛP ΛR hP hR i (corner i) Z δ sy hc 7

-- The two absent-corner branches keep the same literal padded equations.
private def sourceAbsent (i : Bool) : Sector Bool := (Finsupp.single i 1, 0)
example (i : Bool) : ¬StepValid (true, i) false (sourceAbsent i) := by
  simp [sourceAbsent, StepValid]
example (i : Bool) (Z : P.H (sourceAbsent i))
    (δ : WeightBlocks D ΛR (P.muM (sourceAbsent i))) :=
  elvProbe_content_padded_central_separated_windows_above
    D Sc m cutoff 12 ΛP ΛR hP hR i (sourceAbsent i) Z δ sy hc 7
private def targetAbsent (i : Bool) : Sector Bool := (0, Finsupp.single i 1)
example (i : Bool) : ¬StepValid (false, i) true (targetAbsent i) := by
  simp [targetAbsent, StepValid]
example (i : Bool) (Z : P.H (targetAbsent i))
    (δ : WeightBlocks D ΛR (P.muM (targetAbsent i))) :=
  elvProbe_content_padded_central_separated_windows_above
    D Sc m cutoff 12 ΛP ΛR hP hR i (targetAbsent i) Z δ sy hc 7

example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end ProbePaddedContentBendsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedContentBends
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

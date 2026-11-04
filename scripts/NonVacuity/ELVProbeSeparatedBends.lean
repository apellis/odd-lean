import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSeparatedBends
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeSeparatedBendsConsumer
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

-- The XP-to-YR window retains every supported probe/content input.
example (i : Bool) (t : Sector Bool) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbeDx_separated_windows D Sc m cutoff 12 ΛP ΛR hP hR i t Z M δ sy hc
example (i : Bool) (t : Sector Bool) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbeCx_separated_windows D Sc m cutoff 12 ΛP ΛR hP hR i t hb hv Z M δ sy hc
example (i : Bool) (t : Sector Bool) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbe_central_separated_windows D Sc m cutoff 12 ΛP ΛR hP hR i t hb hv Z M δ sy hc

private def corner (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)
private theorem hb (i : Bool) : StepValid (false, i) true (corner i) := by
  simp [corner, StepValid]
private theorem hv (i : Bool) : StepValid (true, i) false (corner i) := by
  simp [corner, StepValid]

-- Both parity corners use one common count in the literal hDx/hCx equations.
example (Z : P.H (corner false)) (M : P.T.obj (-P.muP (corner false)))
    (δ : WeightBlocks D ΛR (P.muM (corner false))) :
    ∃ N, ELVProbeDxSeparatedAt D Sc m cutoff 12 ΛP ΛR hP hR false (corner false) Z M δ sy hc N ∧
      ELVProbeCxSeparatedAt D Sc m cutoff 12 ΛP ΛR hP hR false (corner false)
        (hb false) (hv false) Z M δ sy hc N :=
  elvProbe_central_separated_windows D Sc m cutoff 12 ΛP ΛR hP hR false (corner false)
    (hb false) (hv false) Z M δ sy hc
example (Z : P.H (corner true)) (M : P.T.obj (-P.muP (corner true)))
    (δ : WeightBlocks D ΛR (P.muM (corner true))) :
    ∃ N, ELVProbeDxSeparatedAt D Sc m cutoff 12 ΛP ΛR hP hR true (corner true) Z M δ sy hc N ∧
      ELVProbeCxSeparatedAt D Sc m cutoff 12 ΛP ΛR hP hR true (corner true)
        (hb true) (hv true) Z M δ sy hc N :=
  elvProbe_central_separated_windows D Sc m cutoff 12 ΛP ΛR hP hR true (corner true)
    (hb true) (hv true) Z M δ sy hc
-- A requested finite inverse-window height is absorbed before choosing the bound.
example (i : Bool) (Z : P.H (corner i)) (M : P.T.obj (-P.muP (corner i)))
    (δ : WeightBlocks D ΛR (P.muM (corner i))) (minimum : ℕ) :=
  elvProbe_central_separated_windows_above D Sc m cutoff 12 ΛP ΛR hP hR i (corner i)
    (hb i) (hv i) Z M δ sy hc minimum
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end ProbeSeparatedBendsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.SeparatedBendSeries,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeSeparatedBends] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    logInfo m!"Auditing {names.size} owned declarations in {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"

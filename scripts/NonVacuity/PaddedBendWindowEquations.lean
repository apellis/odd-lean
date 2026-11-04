import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSeparatedBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWindowEquations
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.SKM
namespace PaddedBendWindowConsumer
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

private instance contentZero (β : Multiset Bool) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff 12 β) :=
  ⟨⟨_, elvZeroModule_isZero D (parameterTwist D Sc) cutoff 12 β⟩⟩

private theorem hd (i : Bool) {a b : Bool → ℤ} (h : a + D.α i = b) :
    IsIso (P.T.dot i h) :=
  elvProbeFactorDot_isIso D Sc m cutoff 12 ΛP ΛR hP hR i h

-- Arbitrary supported Hom objects retain both padded bends at one requested height.
private theorem padded_windows (i : Bool) (t : Sector Bool) (hb : StepValid (dn i) true t)
    (hv : StepValid (up i) false t) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) (minimum : ℕ) :
    let E := elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR t M δ
    ∃ N, minimum ≤ N ∧ P.CentralPaddedDxSeparatedAt i t Z E (hd i)
        (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc) N ∧
      P.CentralPaddedCxSeparatedAt i t Z E (hd i)
        (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc) N := by
  obtain ⟨N, hN, hD, hC⟩ := elvProbe_central_separated_windows_above
    D Sc m cutoff 12 ΛP ΛR hP hR i t hb hv Z M δ sy hc minimum
  exact ⟨N, hN, P.centralPaddedDx_separated i t Z _ (hd i) _ N hD,
    P.centralPaddedCx_separated i t Z _ (hd i) _ hb hv N hC⟩

private def corner (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)
private theorem hb (i : Bool) : StepValid (dn i) true (corner i) := by
  simp [corner, StepValid]
private theorem hv (i : Bool) : StepValid (up i) false (corner i) := by
  simp [corner, StepValid]
example (i : Bool) (Z : P.H (corner i)) (M : P.T.obj (-P.muP (corner i)))
    (δ : WeightBlocks D ΛR (P.muM (corner i))) (minimum : ℕ) :=
  padded_windows i (corner i) (hb i) (hv i) Z M δ minimum

-- At the empty sector both absent corners remain in the literal padded equation.
private def emptySector : Sector Bool := (0, 0)
private theorem hsource (i : Bool) : ¬StepValid (up i) false emptySector := by
  simp [StepValid, emptySector]
private theorem htarget (i : Bool) : ¬StepValid (dn i) true emptySector := by
  simp [StepValid, emptySector]
example (i : Bool) (Z : P.H emptySector) (M : P.T.obj (-P.muP emptySector))
    (δ : WeightBlocks D ΛR (P.muM emptySector)) (N : ℕ) :=
  P.centralPaddedCx_separated_of_source_absent i emptySector Z
    (elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR emptySector M δ)
    (hd i) (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc) (hsource i) N
example (i : Bool) (Z : P.H emptySector) (M : P.T.obj (-P.muP emptySector))
    (δ : WeightBlocks D ΛR (P.muM emptySector)) (N : ℕ) :=
  P.centralPaddedCx_separated_of_target_absent i emptySector Z
    (elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR emptySector M δ)
    (hd i) (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc) (htarget i) N

example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end PaddedBendWindowConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWindowEquations
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  logInfo m!"Auditing {names.size} owned declarations in {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

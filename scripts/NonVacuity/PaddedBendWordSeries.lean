import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSeparatedBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWordSeries
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace PaddedBendWordSeriesConsumer
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
private def P := elvProbeReservoir D Sc m cutoff 12 ΛP ΛR hP hR
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

private theorem hd (i : Bool) {a b : Bool → ℤ} (h : a + D.α i = b) :
    IsIso (P.T.dot i h) :=
  elvProbeFactorDot_isIso D Sc m cutoff 12 ΛP ΛR hP hR i h
local notation "out" "[" t "," M "," δ "]" =>
  elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR t M δ
local notation "c" => elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc
private instance (β : Multiset Bool) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff 12 β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff 12 β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff 12 β⟩⟩

-- The known ELV finite bend supplies its exact finite-equation premise.
private def window (i : Bool) (t : Sector Bool) (Z : P.H t)
    (M : P.T.obj (-P.muP t)) (δ : WeightBlocks D ΛR (P.muM t)) : ℕ :=
  Classical.choose (elvProbeDx_separated_windows
    D Sc m cutoff 12 ΛP ΛR hP hR i t Z M δ sy hc)
private theorem window_equation (i : Bool) (t : Sector Bool) (Z : P.H t)
    (M : P.T.obj (-P.muP t)) (δ : WeightBlocks D ΛR (P.muM t)) :
    P.CentralPaddedDxSeparatedAt i t Z out[t,M,δ] (hd i) c (window i t Z M δ) :=
  P.centralPaddedDx_separated i t Z out[t,M,δ] (hd i) c _
    (Classical.choose_spec (elvProbeDx_separated_windows
      D Sc m cutoff 12 ΛP ΛR hP hR i t Z M δ sy hc))
example (i : Bool) (t : Sector Bool) (Z : P.H t)
    (M : P.T.obj (-P.muP t)) (δ : WeightBlocks D ΛR (P.muM t)) :=
  P.centralPaddedDx_word_series i t Z out[t,M,δ] (hd i) c (window i t Z M δ)
    (window_equation i t Z M δ)

example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end PaddedBendWordSeriesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWordSeries
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

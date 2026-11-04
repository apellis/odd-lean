import OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeSeparatedSeriesConsumer
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

private def corner (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)
private theorem hb (i : Bool) : StepValid (false, i) true (corner i) := by
  simp [corner, StepValid]
private theorem hv (i : Bool) : StepValid (true, i) false (corner i) := by
  simp [corner, StepValid]

-- The chosen coefficient, inverse, whole factor unit and bound are constructed.
example (t : Sector Bool) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  let _ : IsIso (P.T.dot false (P.muP_preE false t)) :=
    (isUnit_iff_isIso _).mp (elvProbeReservoir_dot_isUnit D Sc m cutoff 12 ΛP ΛR hP hR false (P.muP_preE false t))
  probeToReservoirBend_even_separated (C := ContentModules D (parameterTwist D Sc) cutoff 12 δ.1)
    P false t Z (elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR t M δ)
    (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff 12 ΛP ΛR hP hR sy hc) rfl
    (Classical.choose (elvProbeDxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR false t Z M δ sy hc))
    (Classical.choose_spec (elvProbeDxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR false t Z M δ sy hc))

-- The chosen coefficient, inverse, whole factor unit and bound are constructed.
example (t : Sector Bool) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  let _ : IsIso (P.T.dot true (P.muP_preE true t)) :=
    (isUnit_iff_isIso _).mp (elvProbeReservoir_dot_isUnit D Sc m cutoff 12 ΛP ΛR hP hR true (P.muP_preE true t))
  probeToReservoirBend_odd_separated (C := ContentModules D (parameterTwist D Sc) cutoff 12 δ.1)
    P true t Z (elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR t M δ)
    (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff 12 ΛP ΛR hP hR sy hc) rfl
    (Classical.choose (elvProbeDxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR true t Z M δ sy hc))
    (Classical.choose_spec (elvProbeDxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR true t Z M δ sy hc))

-- The chosen coefficient, inverse, whole factor unit and bound are constructed.
example (Z : P.H (corner false)) (M : P.T.obj (-P.muP (corner false)))
    (δ : WeightBlocks D ΛR (P.muM (corner false))) :=
  let _ : IsIso (P.T.dot false (P.muP_preF false (hb false))) :=
    (isUnit_iff_isIso _).mp (elvProbeReservoir_dot_isUnit D Sc m cutoff 12 ΛP ΛR hP hR false (P.muP_preF false (hb false)))
  reservoirToProbeBend_even_separated (C := ContentModules D (parameterTwist D Sc) cutoff 12 δ.1)
    P false (corner false) (hb false) (hv false) Z (elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR (corner false) M δ)
    (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff 12 ΛP ΛR hP hR sy hc) rfl
    (Classical.choose (elvProbeCxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR false (corner false) (hb false) (hv false) Z M δ sy hc))
    (Classical.choose_spec (elvProbeCxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR false (corner false) (hb false) (hv false) Z M δ sy hc))

-- The chosen coefficient, inverse, whole factor unit and bound are constructed.
example (Z : P.H (corner true)) (M : P.T.obj (-P.muP (corner true)))
    (δ : WeightBlocks D ΛR (P.muM (corner true))) :=
  let _ : IsIso (P.T.dot true (P.muP_preF true (hb true))) :=
    (isUnit_iff_isIso _).mp (elvProbeReservoir_dot_isUnit D Sc m cutoff 12 ΛP ΛR hP hR true (P.muP_preF true (hb true)))
  reservoirToProbeBend_odd_separated (C := ContentModules D (parameterTwist D Sc) cutoff 12 δ.1)
    P true (corner true) (hb true) (hv true) Z (elvProbeBendOutputEvaluation D Sc m cutoff 12 ΛP ΛR hP hR (corner true) M δ)
    (elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff 12 ΛP ΛR hP hR sy hc) rfl
    (Classical.choose (elvProbeCxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR true (corner true) (hb true) (hv true) Z M δ sy hc))
    (Classical.choose_spec (elvProbeCxOuterDot_isNilpotent D Sc m cutoff 12 ΛP ΛR hP hR true (corner true) (hb true) (hv true) Z M δ sy hc))

example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end ProbeSeparatedSeriesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.SeparatedBendSeries,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    logInfo m!"Auditing {names.size} owned declarations in {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"

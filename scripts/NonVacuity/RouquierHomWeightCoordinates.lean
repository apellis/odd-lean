import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedContentBends
import OddMath.SKM.RouquierHomWeightCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace RouquierHomWeightCoordinatesConsumer
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

private theorem hd (i : Bool) {a b : Bool → ℤ} (h : a + D.α i = b) :
    IsIso (P.T.dot i h) :=
  SupportedSectors.probeWindowDot_isIso D Sc m cutoff 12 ΛP ΛR hP hR i h
private theorem zeroP : P.muP (0,0) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
private theorem zeroR : P.muM (0,0) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

-- Both formal vacuum weights change presentation. The same literal
-- negative-cap and dotted-unit word is retained at every pair of powers.
example (i : Bool) (n r : ℕ)
    (Z : SKM.homWeightSector P.T.obj P.W.obj ΛP (-ΛR)) :=
  SKM.homCapCup_weight_pullback_square P.T P.W zeroP zeroR i
    (P.muP_preE i (0,0)) (P.muM_postF i (0,0)) 0 Z (hd i) n r

example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end RouquierHomWeightCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierHomWeightCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

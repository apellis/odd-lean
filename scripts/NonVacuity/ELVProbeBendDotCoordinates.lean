import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendDotCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeBendDotCoordinatesConsumer
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

-- The native XP-to-YR coefficient is tested at the prescribed lowered Hom object.
example (i : Bool) (t : Sector Bool) (Z : P.H t) :=
  P.probeToReservoirCoefficientIso_preDot i t
    ((SKM.homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)
example (i : Bool) (t : Sector Bool) (Z : P.H t) :=
  P.probeToReservoirCoefficientIso_postDot i t
    ((SKM.homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)

-- Both pure corners occur at this specified nonempty sector.
private def corner (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)
private theorem hb (i : Bool) : StepValid (false, i) true (corner i) := by
  simp [corner, StepValid]
private theorem hv (i : Bool) : StepValid (true, i) false (corner i) := by
  simp [corner, StepValid]
example (i : Bool) (Z : P.H (corner i)) :=
  P.reservoirToProbeCoefficientChart_preDot i (corner i) (hb i) (hv i)
    ((SKM.homContentPostF P.T.obj P.W i (corner i).1 (P.muP (corner i))
      (P.muM_postE i (hv i))).obj Z)
example (i : Bool) (Z : P.H (corner i)) :=
  P.reservoirToProbeCoefficientChart_postDot i (corner i) (hb i) (hv i)
    ((SKM.homContentPostF P.T.obj P.W i (corner i).1 (P.muP (corner i))
      (P.muM_postE i (hv i))).obj Z)
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end ProbeBendDotCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.BendDotCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

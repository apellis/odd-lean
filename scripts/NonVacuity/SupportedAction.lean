import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.SwappedAssembly
namespace SupportedActionConsumer
local instance homPi (A B : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private def cutoff : Bool → ℕ := fun _ => 4
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private def ΛR : Bool → ℤ := fun _ => 4
private theorem hP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i ΛP := rfl
private theorem hR (i : Bool) : (cutoff i : ℤ) = D.h i ΛR := rfl
private def sy : Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def powers (_ : Bool × ℕ) : ℕ := 3
private abbrev N := PowerWordContent.powerBound D cutoff powers
private abbrev P := elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
private abbrev c := elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc
private abbrev L := SupportedSectors.pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc
private def Gs := SupportedSectors.tensorSourceFamily D Sc m cutoff ΛP ΛR powers [false, true]
private def Ys := SupportedSectors.tensorTargetFamily D Sc m cutoff ΛP ΛR powers

-- The exact native obligations use the prescribed mixed-parity word row and vacuum family.
example : SwappedObligations Sc (P.layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
    (P.swappedGens c L)) :=
  SupportedSectors.pointwiseObligations D Sc m cutoff N ΛP ΛR hP hR sy hc Gs Ys
example : UpwardModuleAction D Sc (ΛP - ΛR) :=
  SupportedSectors.pointwiseUpwardModuleAction D Sc m cutoff N ΛP ΛR hP hR sy hc Gs Ys (ΛP - ΛR)

example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end SupportedActionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.SupportedInversionRelations,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedSupernaturality,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedAction] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}: standard axioms only"

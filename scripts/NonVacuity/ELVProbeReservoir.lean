import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import NonVacuity.ELVWeightedAppendFixture
import OddMath.SKM.RouquierFTriangle
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeReservoirConsumer
local instance piSCatHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev D := WeightedAppendFixture.datum
private abbrev S := WeightedAppendFixture.scalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def W (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β => N β.1.toList
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem diff (i : Bool) : i ≠ !i := by cases i <;> decide

private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private def reservoirCutoff : Bool → ℕ := fun _ => 4
private def reservoirHighest : Bool → ℤ := fun _ => 4
private theorem reservoirPairing (i : Bool) : (reservoirCutoff i : ℤ) = D.h i reservoirHighest := rfl
private abbrev P := elvProbeReservoir D S m reservoirCutoff 12 Λ reservoirHighest probePairing reservoirPairing
example : ProbeReservoir ℚ (PiSCat.{0,0,1} ℚ) D S := P
example := elvProbeReservoir_T D S m reservoirCutoff 12 Λ reservoirHighest probePairing reservoirPairing
example := elvProbeReservoir_W D S m reservoirCutoff 12 Λ reservoirHighest probePairing reservoirPairing
example := elvProbeReservoir_leftAdj D S m reservoirCutoff 12 Λ reservoirHighest probePairing reservoirPairing
example (i : Bool) := elvProbeReservoir_dot_isUnit D S m reservoirCutoff 12 Λ reservoirHighest
  probePairing reservoirPairing i (x := -Λ) rfl
example : P.muP (0,0) = Λ := by simp only [ProbeReservoir.muP, map_zero, sub_zero]
example : P.muM (0,0) = -reservoirHighest := by simp only [ProbeReservoir.muM, map_zero, add_zero]
end ProbeReservoirConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

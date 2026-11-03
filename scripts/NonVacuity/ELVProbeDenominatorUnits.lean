import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeDenominatorUnitsConsumer
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
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : S.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def denominators := elvProbeCrossDenominatorUnits D S m reservoirCutoff 12
  Λ reservoirHighest probePairing reservoirPairing sy hc
private def coefficient := elvProbeCrossCoeff D S m reservoirCutoff 12
  Λ reservoirHighest probePairing reservoirPairing sy hc
private theorem inverse : coefficient.IsInverse :=
  elvProbeCrossCoeff_isInverse D S m reservoirCutoff 12
    Λ reservoirHighest probePairing reservoirPairing sy hc

-- Whole statements on the complete factor pair, at each of its even and odd colours.
example := denominators.even false rfl
example := denominators.odd true rfl
example := inverse.even false rfl
example := inverse.odd true rfl

-- The actual scalar-probe induction has a nonzero input witness at both parities.
example (i : Bool) : probeOldVacuumAppendVector D S m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D S m i (by cases i <;> decide)
example (i : Bool) := elvProbeReservoir_dot_isUnit D S m reservoirCutoff 12
  Λ reservoirHighest probePairing reservoirPairing i (x := -Λ) rfl

private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private def Λo : Bool → ℤ := fun i => probeCutoff Do m i
private theorem hPo (i : Bool) : (probeCutoff Do m i : ℤ) = Do.h i Λo := rfl
private theorem hRo (i : Bool) : (reservoirCutoff i : ℤ) = Do.h i reservoirHighest := rfl
private def oddDenominators := elvProbeCrossDenominatorUnits Do So m reservoirCutoff 12
  Λo reservoirHighest hPo hRo AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous
private def oddCoefficient := elvProbeCrossCoeff Do So m reservoirCutoff 12
  Λo reservoirHighest hPo hRo AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous
example (i : Bool) := oddDenominators.odd i rfl
example (i : Bool) :=
  (elvProbeCrossCoeff_isInverse Do So m reservoirCutoff 12 Λo reservoirHighest hPo hRo
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous).odd i rfl
example (i : Bool) : probeOldVacuumAppendVector Do So m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero Do So m i (by cases i <;> decide)

end ProbeDenominatorUnitsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

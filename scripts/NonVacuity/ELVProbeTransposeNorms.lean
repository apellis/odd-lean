import OddMath.QuiverHecke.CyclotomicAction.ELVProbeTransposeNorms
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeTransposeNormsConsumer
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
private theorem denominators : P.CrossDenominatorUnits := elvProbeCrossDenominatorUnits D S m reservoirCutoff 12
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
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)
example (i : Bool) := elvProbeReservoir_dot_isUnit D S m reservoirCutoff 12
  Λ reservoirHighest probePairing reservoirPairing i (x := -Λ) rfl

private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private def Λo : Bool → ℤ := fun i => probeCutoff Do m i
private theorem hPo (i : Bool) : (probeCutoff Do m i : ℤ) = Do.h i Λo := rfl
private theorem hRo (i : Bool) : (reservoirCutoff i : ℤ) = Do.h i reservoirHighest := rfl
private abbrev Po := elvProbeReservoir Do So m reservoirCutoff 12
  Λo reservoirHighest hPo hRo
private theorem oddDenominators : Po.CrossDenominatorUnits := elvProbeCrossDenominatorUnits Do So m reservoirCutoff 12
  Λo reservoirHighest hPo hRo AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous
private def oddCoefficient := elvProbeCrossCoeff Do So m reservoirCutoff 12
  Λo reservoirHighest hPo hRo AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous
example (i : Bool) := oddDenominators.odd i rfl
example (i : Bool) :=
  (elvProbeCrossCoeff_isInverse Do So m reservoirCutoff 12 Λo reservoirHighest hPo hRo
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous).odd i rfl
example (i : Bool) : probeOldVacuumAppendVector Do (parameterTwist Do So) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero Do (parameterTwist Do So) m i (by cases i <;> decide)
example : coefficient.IsSupernatural :=
  elvProbeCrossCoeff_isSupernatural D S m reservoirCutoff 12
    Λ reservoirHighest probePairing reservoirPairing sy hc
example : oddCoefficient.IsSupernatural :=
  elvProbeCrossCoeff_isSupernatural Do So m reservoirCutoff 12
    Λo reservoirHighest hPo hRo AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous

private theorem norms : P.CrossTransposeNormUnits :=
  ELVProbeCrossTransposeNormUnits D S m reservoirCutoff 12 Λ reservoirHighest
    probePairing reservoirPairing sy hc
private theorem swaps : P.SwappingInvertible coefficient :=
  elvProbeSwappingInvertible D S m reservoirCutoff 12 Λ reservoirHighest
    probePairing reservoirPairing sy hc
example := norms.even false rfl (xP := -Λ) (yP := -Λ + D.α false)
  (xW := -reservoirHighest) (yW := -reservoirHighest + D.α false)
example := norms.odd_sub true rfl (xP := -Λ) (yP := -Λ + D.α true)
  (xW := -reservoirHighest) (yW := -reservoirHighest + D.α true)
example := norms.odd_add true rfl (xP := -Λ) (yP := -Λ + D.α true)
  (xW := -reservoirHighest) (yW := -reservoirHighest + D.α true)
example : P.SwappingInvertible coefficient := swaps

/-- Literal arbitrary source Hom, with a nontrivial parity shift and the actual probe dot. -/
example (H : P.T.obj (-Λ + D.α false) ⟶ P.W.obj (-reservoirHighest + D.α false)) :=
  norms.even false rfl (show -Λ + D.α false = -Λ + D.α false from rfl)
    (show -reservoirHighest + D.α false = -reservoirHighest + D.α false from rfl) 1 H
example (H : P.T.obj (-Λ + D.α true) ⟶ P.W.obj (-reservoirHighest + D.α true)) :=
  norms.odd_sub true rfl (show -Λ + D.α true = -Λ + D.α true from rfl)
    (show -reservoirHighest + D.α true = -reservoirHighest + D.α true from rfl) 1 H
example (H : P.T.obj (-Λ + D.α true) ⟶ P.W.obj (-reservoirHighest + D.α true)) :=
  norms.odd_add true rfl (show -Λ + D.α true = -Λ + D.α true from rfl)
    (show -reservoirHighest + D.α true = -reservoirHighest + D.α true from rfl) 1 H

private theorem oddNorms : Po.CrossTransposeNormUnits :=
  ELVProbeCrossTransposeNormUnits Do So m reservoirCutoff 12 Λo reservoirHighest hPo hRo
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous
example (i : Bool) := oddNorms.odd_sub i rfl (xP := -Λo) (yP := -Λo + Do.α i)
  (xW := -reservoirHighest) (yW := -reservoirHighest + Do.α i)
example (i : Bool) := oddNorms.odd_add i rfl (xP := -Λo) (yP := -Λo + Do.α i)
  (xW := -reservoirHighest) (yW := -reservoirHighest + Do.α i)
example : Po.SwappingInvertible oddCoefficient :=
  elvProbeSwappingInvertible Do So m reservoirCutoff 12 Λo reservoirHighest hPo hRo
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous

end ProbeTransposeNormsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.RouquierHomDistinctMixedPostDotsIso,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeTransposeNorms,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceNorms,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceOddNorms] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"

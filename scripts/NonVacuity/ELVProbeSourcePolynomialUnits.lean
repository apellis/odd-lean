import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSourcePolynomialUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeSourcePolynomialUnitsConsumer
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

private abbrev sourceUnits := elvProbeMixedPostSourceUnits D S m reservoirCutoff 12
  Λ reservoirHighest probePairing reservoirPairing sy hc
example := sourceUnits false true (a := -Λ) (b := -Λ + D.α false)
  (c := -reservoirHighest) (d := -reservoirHighest + D.α true)
example := sourceUnits true false (a := -Λ) (b := -Λ + D.α true)
  (c := -reservoirHighest) (d := -reservoirHighest + D.α false)
example := sourceUnits true true (a := -Λ) (b := -Λ + D.α true)
  (c := -reservoirHighest) (d := -reservoirHighest + D.α true)

example (H : P.T.obj (-Λ + D.α false) ⟶ P.W.obj (-reservoirHighest + D.α true)) :=
  sourceUnits false true (show -Λ + D.α false = -Λ + D.α false from rfl)
    (show -reservoirHighest + D.α true = -reservoirHighest + D.α true from rfl) 1 H
example (H : P.T.obj (-Λ + D.α true) ⟶ P.W.obj (-reservoirHighest + D.α false)) :=
  sourceUnits true false (show -Λ + D.α true = -Λ + D.α true from rfl)
    (show -reservoirHighest + D.α false = -reservoirHighest + D.α false from rfl) 1 H

-- A genuine positive-post-dot monomial, with arbitrary coefficient unit and leading degree.
example (H : P.T.obj (-Λ + D.α true) ⟶ P.W.obj (-reservoirHighest + D.α false))
    (c : ℚˣ) (n : ℕ) :=
  sourceUnits true false (show -Λ + D.α true = -Λ + D.α true from rfl)
    (show -reservoirHighest + D.α false = -reservoirHighest + D.α false from rfl) 1 H
    c n _ (Submodule.subset_span ⟨2, 3, trivial, trivial, by decide, rfl⟩)

example := elvProbe_distinct_sigmaEntry_isIso D S m reservoirCutoff 12
  Λ reservoirHighest probePairing reservoirPairing sy hc coefficient (i := false) (j := true)
example := elvProbeMixedPostSourceUnits Do So m reservoirCutoff 12 Λo reservoirHighest hPo hRo
  AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous false true
  (a := -Λo) (b := -Λo + Do.α false)
  (c := -reservoirHighest) (d := -reservoirHighest + Do.α true)
example := elvProbe_distinct_sigmaEntry_isIso Do So m reservoirCutoff 12 Λo reservoirHighest hPo hRo
  AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous oddCoefficient (i := false) (j := true)

end ProbeSourcePolynomialUnitsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.RouquierHomDistinctSourceUnits,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntrySourceUnits,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourcePolynomialUnits,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeSourcePolynomialUnits] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"

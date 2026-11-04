import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSigmaPermutation
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.SwappedAssembly
namespace ELVProbeSigmaPermutationConsumer
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
private abbrev P := elvProbeReservoir D Sc m cutoff 12 ΛP ΛR hP hR
private abbrev c := elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc
-- The intermediate assembly retains exactly the canonical factor left-mate input.
example (hL : LeftMateInvertible P.T P.T.leftAdjoints) : P.SigmaPermutation c false true 0 :=
  elvProbeSigmaPermutation_of_leftMateInvertible D Sc m cutoff 12 ΛP ΛR hP hR sy hc hL
    false true 0 (by decide)

example (ν : Bool → ℤ) (t s : Sector Bool)
    (p : SPath (wd D ν [up true, dn false]) t s)
    (q : SPath (wd D ν [dn false, up true]) t s)
    (hp : p.sides = [false, false]) (hq : q.sides = [false, false]) (Z : P.H s) :
    IsIso (P.sigmaEntry c false true ν p q Z) :=
  P.isIso_sigmaEntry_pure_reservoir c (by decide) ν p q hp hq Z

-- Both mixed entries are proved on the full prescribed Hom category.
example (ν : Bool → ℤ) (t : Sector Bool)
    (q : SPath (wd D ν [dn false, up true]) t
      (nextSector (dn false) false (nextSector (up true) true t)))
    (Z : P.H (nextSector (dn false) false (nextSector (up true) true t))) :
    IsIso (P.sigmaEntry c false true ν
      (SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))) q Z) :=
  elvProbe_distinct_sigmaEntry_isIso D Sc m cutoff 12 ΛP ΛR hP hR sy hc c
    (by decide) ν t q Z
example (ν : Bool → ℤ) (t s : Sector Bool)
    (p : SPath (wd D ν [up true, dn false]) t s)
    (q : SPath (wd D ν [dn false, up true]) t s)
    (hp : p.sides = [false, true]) (hq : q.sides = [true, false]) (Z : P.H s) :
    IsIso (P.sigmaEntry c false true ν p q Z) :=
  P.isIso_sigmaEntry_reservoir_probe c (by decide) ν p q hp hq Z
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end ELVProbeSigmaPermutationConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVProbeSigmaPermutation,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureEntries,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureReservoirEntry,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctReservoirShift] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}: standard axioms only"

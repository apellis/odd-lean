import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureReservoirEntry
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSigmaPermutation
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.DistinctPureReservoirEntry
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
private def t : Sector Bool := (0, Finsupp.single false 1 + Finsupp.single true 1)
private def s := nextSector (dn false) false (nextSector (up true) false t)
private theorem target_eq :
    nextSector (up true) false (nextSector (dn false) false t) = s := by
  classical
  apply Prod.ext
  · rfl
  · ext i
    cases i <;> simp [s, t, nextSector, Finsupp.coe_tsub]
private def p : SPath (wd D 0 [up true, dn false]) t s :=
  .cons _ false t (by classical simp [StepValid, t])
    (.cons _ false _ trivial (.nil _))
private def q : SPath (wd D 0 [dn false, up true]) t s :=
  .cons _ false t trivial
    (.cons _ false _ (by classical simp [StepValid, t, nextSector])
      ((SPath.nil _).castTgt target_eq))

example (Z : P.H s) : IsIso (P.sigmaEntry c false true 0 p q Z) :=
  P.isIso_sigmaEntry_pure_reservoir c (by decide) 0 p q
    (by simp [p, SPath.sides]) (by simp [q, SPath.sides]) Z
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end NonVacuity.DistinctPureReservoirEntry

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureReservoirEntry
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

import OddMath.QuiverHecke.SwappedAssembly.Sigma.OffCentralAugmentedMatrix
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeTransposeNorms
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.SwappedAssembly
namespace OffCentralAugmentedMatrixConsumer
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
private abbrev P := elvProbeReservoir D Sc m cutoff 12 ΛP ΛR hP hR
private def sy : Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private abbrev c := elvProbeCrossCoeff D Sc m cutoff 12 ΛP ΛR hP hR sy hc
private def t : Sector Bool := (0, 0)
private def s (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)
private theorem hts (i : Bool) : t ≠ s i := by
  intro h
  have e := congrArg (fun z : Sector Bool => z.1 i) h
  simpa [t, s] using e

-- Both path families are occupied; the identity-window family is empty.
private def p (i : Bool) : SPath (wd D 0 [up i, dn i]) t (s i) :=
  SPath.cons _ true t trivial (SPath.cons _ false _ trivial (by
    simpa [nextSector, t, s] using SPath.nil (s i)))
private def q (i : Bool) : SPath (wd D 0 [dn i, up i]) t (s i) :=
  SPath.cons _ false t trivial (SPath.cons _ true _ trivial (by
    simpa [nextSector, t, s] using SPath.nil (s i)))
example (i : Bool) : Nonempty (SPath (wd D 0 [up i, dn i]) t (s i)) ∧
    Nonempty (SPath (wd D 0 [dn i, up i]) t (s i)) := ⟨⟨p i⟩, ⟨q i⟩⟩

-- The hypotheses come from the actual chosen OLD/ELV transposed norms.
example (i : Bool) (Z : P.H (s i)) : IsIso (P.augPosMat c i 0 t (s i) Z) :=
  ProbeReservoir.isIso_augPosMat_of_ne c i 0 (hts i) Z
    (fun p q => elvProbeSwappingInvertible D Sc m cutoff 12 ΛP ΛR hP hR sy hc
      i 0 t (s i) (hts i) p q Z)
example (i : Bool) (Z : P.H (s i)) : IsIso (P.augNegMat c i 0 t (s i) Z) :=
  ProbeReservoir.isIso_augNegMat_of_ne c i 0 (hts i) Z
    (fun p q => elvProbeSwappingInvertible D Sc m cutoff 12 ΛP ΛR hP hR sy hc
      i 0 t (s i) (hts i) p q Z)
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end OffCentralAugmentedMatrixConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.OffCentralAugmentedMatrix
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"

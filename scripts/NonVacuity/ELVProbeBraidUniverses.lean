import OddMath.QuiverHecke.SwappedAssembly.BraidAssembly
import OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.SwappedAssembly
namespace ELVProbeBraidUniversesConsumer
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
private abbrev L := P.leftwardOfPointwiseAugmentedInverse c

-- The actual functor bicategory has objects two universes above its scalar ring.
-- All inverse and denominator hypotheses come from the chosen ELV construction.
example : ProbeReservoir.CrossBraid (P.swappedGens c L) :=
  P.crossBraidOfDenominatorUnits c L
    (elvProbeCrossCoeff_isInverse D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
    (elvProbeCrossDenominatorUnits D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
example (Gs Ys : ∀ s, P.H s) :
    BraidRelations Sc (P.layerRep Gs Ys (P.swappedGens c L)) :=
  P.braidRelationsOfDenominatorUnits c L
    (elvProbeCrossCoeff_isInverse D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
    (elvProbeCrossDenominatorUnits D Sc m cutoff 12 ΛP ΛR hP hR sy hc)
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)
end ELVProbeBraidUniversesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut modules := 0
  let mut declarations := 0
  for idx in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[idx]!
    if owner.toString.startsWith "OddMath.QuiverHecke.SwappedAssembly.Braid" then
      let names := env.header.moduleData[idx]!.constNames
      if names.isEmpty then throwError "Empty owned declarations in {owner}"
      modules := modules + 1
      declarations := declarations + names.size
      for name in names do
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Unexpected axiom {ax} in {name}"
  if modules < 87 then throwError "Expected the generalized braid dependency spine"
  logInfo m!"Audited {declarations} declarations across {modules} braid modules: standard axioms only"

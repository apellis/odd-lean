import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedLocal
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeEvaluatedLocalConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 2 else 4
private def mZero : Bool → ℕ := fun i => if i then 1 else 2
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def unitData (i : Bool) := probeEvaluatedLoc D Sc m [] i
private def capData (i : Bool) := probeEvaluatedLoc D Sc m [i,i] i
private def zeroData (i : Bool) := probeEvaluatedLoc D Sc mZero [] i
example (i : Bool) : probeCutoff D m i = 4 := by cases i <;> decide
example (i : Bool) : probeCutoff D mZero i = 2 := by cases i <;> decide
example (i : Bool) := (unitData i).dot₁_mem
example (i : Bool) := (unitData i).dot₂_mem
example (i : Bool) := (unitData i).cross_mem
example (i : Bool) := (unitData i).slide_left
example (i : Bool) := (unitData i).slide_right
example (i : Bool) := ((unitData i).invNeg (by cases i <;> decide)).total
example (i : Bool) := ((capData i).invPos (by cases i <;> decide)).total
example (i : Bool) := ((zeroData i).invNeg (by cases i <;> decide)).total
example (i : Bool) := ((zeroData i).invPos (by cases i <;> decide)).total
example (i : Bool) := ((unitData i).invNeg (by cases i <;> decide)).gg 0 1
  (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := ((capData i).invPos (by cases i <;> decide)).gg 0 1
  (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) (q : ZMod 2) := probeEvaluatedLoc_invNeg_f'_app D Sc m [] i
  (by cases i <;> decide) q (N [i])
example (i : Bool) (n : ℕ) (q : ZMod 2) := probeEvaluatedLoc_invNeg_g'_app D Sc m [] i
  (by cases i <;> decide) n q (N [i])
example (i : Bool) (q : ZMod 2) := probeEvaluatedLoc_invPos_f'_app D Sc m [i,i] i
  (by cases i <;> decide) q (N [i,i,i])
example (i : Bool) (n : ℕ) (q : ZMod 2) := probeEvaluatedLoc_invPos_g'_app D Sc m [i,i] i
  (by cases i <;> decide) n q (N [i,i,i])
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeEvaluatedLocalConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedLocal
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

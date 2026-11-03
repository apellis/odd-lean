import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace NonVacuity.ELVProbeVacuumUnit
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < m i := by cases i <;> decide

example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (positive i)
example (i : Bool) : probeOrdinaryVacuumAppendVector D Sc m i ≠ 0 :=
  probeOrdinaryVacuumAppendVector_ne_zero D Sc m i (positive i)

private abbrev O := probeOrdinaryVacuumRegular D Sc m
private abbrev target (i : Bool) := probeOrdinaryVacuumAppendTarget D Sc m i
private abbrev V (i : Bool) := Obj (probeOrdinaryAppend D Sc m [] i) O.toFunctor (target i)
private def d (i : Bool) : Module.End ℚ (V i) :=
  transformLinear (probeOrdinaryAppendDot_supernatural D Sc m [] i) O (target i)
private abbrev v (i : Bool) := probeOrdinaryVacuumAppendVector D Sc m i

/-- The prescribed odd signed dot squares to minus one on the occupied coend at m=1. -/
private theorem signed_square : (d false ^ 2) (v false) = -(v false) := by
  have h := probeOrdinaryVacuumInductionDot_odd D Sc m false rfl O (target false)
  change (d false ^ 2 + 1) ^ 1 = 0 at h
  rw [pow_one] at h
  have hh := LinearMap.congr_fun h (v false)
  change (d false ^ 2) (v false) + v false = 0 at hh
  exact eq_neg_of_add_eq_zero_left hh

example : d false (d false (v false)) = -(v false) := signed_square

/-- The raw-minus polynomial fails on this same actual nonzero probe vector. -/
example : (d false ^ 2 - 1) (v false) ≠ 0 := by
  intro h
  have hh : (d false ^ 2) (v false) - v false = 0 := h
  rw [signed_square] at hh
  have hp : v false + v false = 0 := by
    simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, neg_zero] using congrArg Neg.neg hh
  have hs : (2 : ℚ) • v false = 0 := by simpa only [two_smul] using hp
  exact probeOrdinaryVacuumAppendVector_ne_zero D Sc m false (positive false)
    ((smul_eq_zero.mp hs).resolve_left (by norm_num))

end NonVacuity.ELVProbeVacuumUnit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations: {owner}"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

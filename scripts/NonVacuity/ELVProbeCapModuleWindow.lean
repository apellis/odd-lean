import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapModuleWindow
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace NonVacuity.ELVProbeCapModuleWindow
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev K (i : Bool) := oldContentAppend D Sc (probeCutoff D m) [] i

example (i : Bool) (a : ℕ) (ha : a < probeCutoff D m i) :
    ((adjunction (K i)).unit.app N ≫ ProbeVacuumCap.moduleDot D Sc m i ^ a) ≫
      ProbeVacuumCap.cap D Sc m i (positive i) =
        if a + 1 = probeCutoff D m i then 𝟙 N else 0 :=
  ProbeVacuumCap.module_cap_dot_unit D Sc m i (positive i) a ha

/-- Both cutoff 2 and cutoff 4 last rows give the module identity. -/
example (i : Bool) :
    unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N
      (probeCutoff D m i - 1) ≫ ProbeVacuumCap.cap D Sc m i (positive i) = 𝟙 N := by
  have h := ProbeVacuumCap.unitDotColumn_cap D Sc m i (positive i)
    (probeCutoff D m i - 1) (Nat.sub_lt (positive i) (by decide))
  rw [ite_eq_left (Nat.sub_add_cancel (positive i))] at h
  exact h

example (i : Bool) : (ProbeVacuumCap.moduleDot D Sc m i ^ 2 + 1) ^ m i = 0 :=
  ProbeVacuumCap.moduleDot_odd_polynomial D Sc m i (by cases i <;> rfl)

example (i : Bool) : ProbeVacuumCap.moduleDot D Sc m i ∈ parity (R := ℚ) _ _ 1 :=
  ProbeVacuumCap.moduleDot_mem D Sc m i
end NonVacuity.ELVProbeCapModuleWindow
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapModuleWindow
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"

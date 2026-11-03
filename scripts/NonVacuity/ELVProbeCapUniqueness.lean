import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace NonVacuity.ELVProbeCapUniqueness
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev K (i : Bool) := oldContentAppend D Sc (probeCutoff D m) [] i

/-- All criterion hypotheses are supplied by the actual normalized cap;
the probe modules and their prescribed rows are nonzero. -/
example (i : Bool) : (𝟙 (ProbeVacuumCap.source D Sc m i)) ≫
    ProbeVacuumCap.cap D Sc m i (positive i) = ProbeVacuumCap.cap D Sc m i (positive i) := by
  apply ProbeVacuumCap.cap_eq_of_unitDot_window D Sc m i (positive i)
  intro a ha
  rw [Category.id_comp]
  exact ProbeVacuumCap.unitDotColumn_cap D Sc m i (positive i) a ha

example (i : Bool) : ProbeVacuumCap.cap D Sc m i (positive i) ≠ 0 :=
  ProbeVacuumCap.cap_ne_zero D Sc m i (positive i)

example (i : Bool) (a : ℕ) (ha : a < probeCutoff D m i) :
    unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a ≫
      ProbeVacuumCap.cap D Sc m i (positive i) =
        if a + 1 = probeCutoff D m i then 𝟙 N else 0 :=
  ProbeVacuumCap.unitDotColumn_cap D Sc m i (positive i) a ha
end NonVacuity.ELVProbeCapUniqueness
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"

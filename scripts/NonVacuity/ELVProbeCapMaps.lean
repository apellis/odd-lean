import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapMaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeCapMaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
example (i : Bool) : ProbeVacuumCap.cap D Sc m i (positive i) ≠ 0 :=
  ProbeVacuumCap.cap_ne_zero D Sc m i (positive i)
example (i : Bool) : Function.Surjective (ProbeVacuumCap.groundRow D Sc m i (positive i)) :=
  ProbeVacuumCap.groundRow_surjective D Sc m i (positive i)
end NonVacuity.ELVProbeCapMaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapWindow
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
-- Proposed snapshot: occupied native regular-probe normalization checks follow.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapWindow] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations: {owner}"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"

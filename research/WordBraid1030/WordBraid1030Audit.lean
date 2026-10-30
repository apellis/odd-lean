import WordBraid1030Consumer
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for owner in #[`WordBraid1030Checked, `WordBraid1030Consumer] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty inventory {owner}"
    for name in names do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    count := count + names.size
    logInfo m!"{owner}: ALL {names.size} private/generated declarations std3"
  logInfo m!"Complete total {count} declarations std3"

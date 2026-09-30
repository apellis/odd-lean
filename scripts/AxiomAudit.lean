import OddMath
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Audit by owning module, not declaration namespace: this includes private declarations,
compiler-generated auxiliaries, and declarations placed in foreign namespaces.
`scripts/audit_axioms.py` imports every local module and checks the source inventory first. -/
set_option maxHeartbeats 80000000 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let modules := moduleNames.filter (fun n => n.getRoot == `OddMath)
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  let mut foreignCount : Nat := 0
  let mut rows := "module\tdeclaration\taxioms\n"
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx.toNat]!
      if owner.getRoot == `OddMath then
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name} (module {owner})"
        count := count + 1
        if name.getRoot == `_private then
          privateCount := privateCount + 1
        else if name.getRoot != `OddMath then
          foreignCount := foreignCount + 1
        rows := rows ++ s!"{owner}\t{name}\t{String.intercalate "," (axioms.toList.map toString)}\n"
  if count == 0 then
    throwError "No OddMath declarations were imported"
  let expected ← IO.getEnv "ODD_AXIOM_AUDIT_MODULE_COUNT"
  if let some expected := expected then
    unless expected.toNat? == some modules.size do
      throwError "Module inventory mismatch: expected {expected}, imported {modules.size}"
  if let some output ← IO.getEnv "ODD_AXIOM_AUDIT_MODULES" then
    IO.FS.writeFile output (String.intercalate "\n" (modules.toList.map toString) ++ "\n")
  if let some output ← IO.getEnv "ODD_AXIOM_AUDIT_TSV" then
    IO.FS.writeFile output rows
  logInfo m!"Audited {count} declarations owned by {modules.size} OddMath modules; {privateCount} private and {foreignCount} non-OddMath-namespace declarations included. All transitive axioms are allowed."

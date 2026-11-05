import Lean

/-! Dump the declaration-level dependency graph of the `OddMath` declarations of the current
environment. Run with a header importing every `OddMath` module. Output: one line per declaration,
`id<TAB>module<TAB>kind<TAB>name<TAB>dep ids` (dependencies restricted to `OddMath` declarations;
type and value both count). -/

open Lean Elab Command

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let mut ids : Std.HashMap Name Nat := {}
  let mut decls : Array (Name × Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx.toNat]!
      if owner.getRoot == `OddMath then
        ids := ids.insert name decls.size
        decls := decls.push (name, owner, info)
  let some out ← IO.getEnv "ODD_DECL_GRAPH" | throwError "set ODD_DECL_GRAPH"
  let h ← IO.FS.Handle.mk out .write
  for i in [0:decls.size] do
    let (name, owner, info) := decls[i]!
    let deps := info.getUsedConstantsAsSet.toList.filterMap (fun n => ids[n]?)
    h.putStrLn s!"{i}\t{owner}\t{kindOf info}\t{name}\t{String.intercalate " " (deps.map toString)}"
  h.flush
  logInfo m!"Wrote {decls.size} declarations"

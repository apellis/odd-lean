import Lean

/-! Dump the declaration-level dependency graph of the `OddMath` modules from their `.olean` files,
without building an environment (so modules with clashing names can be read together).
Usage: `lake env lean --run scripts/Cleanup/DeclGraph.lean <module list> <output>`.
Output: one line per declaration, `module<TAB>kind<TAB>name<TAB>deps` with dependencies
restricted to declarations of the listed modules (type and value both count). -/

open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def withModule (m : Name) (k : ModuleData → IO Unit) : IO Unit := do
  let path ← findOLean m
  let (d, region) ← readModuleData path
  k d
  region.free

unsafe def main (args : List String) : IO Unit := do
  let [listFile, out] := args | throw (IO.userError "usage: <module list> <output>")
  initSearchPath (← findSysroot)
  let mods := (← IO.FS.lines listFile).filter (· ≠ "") |>.map String.toName
  let known ← IO.mkRef ({} : Std.HashSet String)
  for m in mods do
    withModule m fun d => known.modify fun s => d.constNames.foldl (fun s n => s.insert n.toString) s
  let known ← known.get
  let h ← IO.FS.Handle.mk out .write
  for m in mods do
    withModule m fun d => do
      for c in d.constants do
        let deps := c.getUsedConstantsAsSet.toList.map toString |>.filter known.contains
        h.putStrLn s!"{m}\t{kindOf c}\t{c.name}\t{String.intercalate " " deps}"
  h.flush

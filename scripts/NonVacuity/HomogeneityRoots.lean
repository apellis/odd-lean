import OddMath

open Lean Meta Elab Command

/-- Constants in the proof of `nondegeneracy_of_symmetrizer` whose type mentions
`Scalars.Homogeneous`, and those among them that reference no other such constant. -/
elab "#homogeneity_roots" : command => do
  let env ← getEnv
  let target := ``OddMath.QuiverHecke.nondegeneracy_of_symmetrizer
  let hom := ``OddMath.SKM.Scalars.Homogeneous
  let mentions (n : Name) : Bool :=
    match env.find? n with
    | some ci => ci.type.getUsedConstants.contains hom
    | none => false
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[target]
  let mut hcs : Array Name := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if !(n.getRoot == `OddMath) then continue
    if mentions n then hcs := hcs.push n
    for c in ci.getUsedConstantsAsSet.toArray do
      if !seen.contains c then stack := stack.push c
  logInfo m!"constants in closure: {seen.size}; mentioning Homogeneous: {hcs.size}"
  let mut roots : Array Name := #[]
  for n in hcs do
    let some ci := env.find? n | continue
    let used := ci.getUsedConstantsAsSet.toArray.filter fun c => c != n && mentions c
    if used.isEmpty then roots := roots.push n
  logInfo m!"roots ({roots.size}): {roots.toList}"
  let byMod := hcs.filterMap fun n => (env.getModuleIdxFor? n).map fun i =>
    env.header.moduleNames[i.toNat]!
  let mods := byMod.foldl (fun (s : NameSet) m => s.insert m) {}
  logInfo m!"modules ({mods.size}): {mods.toList}"

#homogeneity_roots

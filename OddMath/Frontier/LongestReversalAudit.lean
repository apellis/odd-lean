import OddMath.Frontier.LongestReversalControls

-- Source types, not merely successful compilation or sampled rank instances.
#check OddMath.Frontier.LongestReversal.action_D
#check OddMath.Frontier.LongestReversal.D_reversed_staircase
#check OddMath.Frontier.LongestReversal.action_D_left_kernel
#check OddMath.Frontier.LongestReversal.triangle_source
#check OddMath.Frontier.LongestReversal.triangle_other
#check OddMath.Frontier.LongestReversalControls.missing_sign_rejected
#check OddMath.Frontier.LongestReversalControls.rank_two_input_not_kernel

-- Module ownership includes safe compiler-named declarations. Only individually
-- identified, genuinely unsafe compiler artifacts are classified separately.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.LongestReversal,
        `OddMath.Frontier.LongestReversalControls,
        `OddMath.Frontier.LongestReversalAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``OddMath.Frontier.LongestReversal.action_D,
      ``OddMath.Frontier.LongestReversal.D_reversed_staircase,
      ``OddMath.Frontier.LongestReversal.action_D_left_kernel,
      ``OddMath.Frontier.LongestReversal.triangle_source,
      ``OddMath.Frontier.LongestReversal.hill_valley,
      ``OddMath.Frontier.LongestReversalControls.missing_sign_rejected] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compilerName := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compilerName && info.isUnsafe then
      stages := stages + 1
      Lean.logInfo m!"COMPILER-UNSAFE '{name}' depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-unsafe={stages}"

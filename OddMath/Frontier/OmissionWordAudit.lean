import OddMath.Frontier.OmissionWordControls

-- Full exported types expose exactly which statements remain conditional.
#check OddMath.Frontier.OmissionWord.generalized_leibniz
#check OddMath.Frontier.OmissionWord.mem_markings
#check OddMath.Frontier.OmissionWord.markings_nodup
#check OddMath.Frontier.OmissionWord.markings_length
#check OddMath.Frontier.OmissionWord.hybrid_allFalse
#check OddMath.Frontier.OmissionWord.term_zero_of_trichotomy
#check OddMath.Frontier.OmissionWord.left_kernel_of_trichotomy
#check OddMath.Frontier.OmissionWord.longest_left_kernel_of_trichotomy
#check OddMath.Frontier.OmissionWordControls.no_termwise_braid_identification
#check OddMath.Frontier.OmissionWordControls.longest_hypothesis_is_essential

-- All safe owned logical declarations, including compiler-named safe helpers.
-- Unsafe generated artifacts are individually printed, not blanket-excluded.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.OmissionWord,
        `OddMath.Frontier.OmissionWordControls,
        `OddMath.Frontier.OmissionWordAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``OddMath.Frontier.OmissionWord.generalized_leibniz,
      ``OddMath.Frontier.OmissionWord.mem_markings,
      ``OddMath.Frontier.OmissionWord.markings_nodup,
      ``OddMath.Frontier.OmissionWord.markings_length,
      ``OddMath.Frontier.OmissionWord.hybrid_allFalse,
      ``OddMath.Frontier.OmissionWord.term_zero_of_trichotomy,
      ``OddMath.Frontier.OmissionWord.left_kernel_of_trichotomy,
      ``OddMath.Frontier.OmissionWord.longest_left_kernel_of_trichotomy,
      ``OddMath.Frontier.OmissionWordControls.no_termwise_braid_identification,
      ``OddMath.Frontier.OmissionWordControls.longest_hypothesis_is_essential] do
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

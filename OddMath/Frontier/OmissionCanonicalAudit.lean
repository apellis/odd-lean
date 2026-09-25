import OddMath.Frontier.OmissionCanonicalControls

-- Exact types: the only word restriction is erase m = the frozen word.
#print OddMath.Frontier.OmissionCanonical.word
#check OddMath.Frontier.OmissionCanonical.word_reduced
#check OddMath.Frontier.OmissionCanonical.word_permutation
#check OddMath.Frontier.OmissionCanonical.block_shape
#check OddMath.Frontier.OmissionCanonical.pair_word_covariance
#check OddMath.Frontier.OmissionCanonical.run_covariance
#check OddMath.Frontier.OmissionCanonical.shaped_block_zero
#check OddMath.Frontier.OmissionCanonical.blocks_zero_or_allFalse
#check OddMath.Frontier.OmissionCanonical.trichotomy
#check OddMath.Frontier.OmissionCanonical.nonexceptional_term_zero
#check OddMath.Frontier.OmissionCanonical.left_kernel
#check OddMath.Frontier.OmissionCanonicalControls.n2
#check OddMath.Frontier.OmissionCanonicalControls.n3
#check OddMath.Frontier.OmissionCanonicalControls.n3_exception_nonreduced

-- No blanket compiler-name exclusion: safe generated helpers are audited.
-- Unsafe code-generation artifacts are explicitly enumerated, never used as proofs.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.OmissionCanonical,
        `OddMath.Frontier.OmissionCanonicalControls,
        `OddMath.Frontier.OmissionCanonicalAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``OddMath.Frontier.OmissionCanonical.word_reduced,
      ``OddMath.Frontier.OmissionCanonical.word_permutation,
      ``OddMath.Frontier.OmissionCanonical.block_shape,
      ``OddMath.Frontier.OmissionCanonical.pair_word_covariance,
      ``OddMath.Frontier.OmissionCanonical.run_covariance,
      ``OddMath.Frontier.OmissionCanonical.shaped_block_zero,
      ``OddMath.Frontier.OmissionCanonical.blocks_zero_or_allFalse,
      ``OddMath.Frontier.OmissionCanonical.trichotomy,
      ``OddMath.Frontier.OmissionCanonical.nonexceptional_term_zero,
      ``OddMath.Frontier.OmissionCanonical.left_kernel,
      ``OddMath.Frontier.OmissionCanonicalControls.n2,
      ``OddMath.Frontier.OmissionCanonicalControls.n3,
      ``OddMath.Frontier.OmissionCanonicalControls.n3_exception_nonreduced] do
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

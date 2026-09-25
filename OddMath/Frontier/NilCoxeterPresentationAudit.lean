import OddMath.Frontier.NilCoxeterPresentationControls

-- Complete transitive logical-axiom audit of BOTH owned modules, generated helpers included.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.NilCoxeterPresentation,
        `OddMath.Frontier.NilCoxeterPresentationControls].contains env.header.moduleNames[idx.toNat]!
    | none => false
  for required in [``OddMath.Frontier.NilCoxeterPresentation.toNilHecke_injective,
      ``OddMath.Frontier.NilCoxeterPresentation.reduced_signed,
      ``OddMath.Frontier.NilCoxeterPresentation.nonreduced_zero,
      ``OddMath.Frontier.NilCoxeterPresentation.mem_basisSpan,
      ``OddMath.Frontier.NilCoxeterPresentation.basis,
      ``OddMath.Frontier.NilCoxeterPresentation.existsUnique_expansion,
      ``OddMath.Frontier.NilCoxeterPresentation.action_injective,
      ``OddMath.Frontier.NilCoxeterPresentation.Controls.quotient_relation_consumer,
      ``OddMath.Frontier.NilCoxeterPresentation.Controls.faithful_consumer] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing production/consumer declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler && info.isUnsafe then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"

set_option pp.fullNames true in
#check OddMath.Frontier.NilCoxeterPresentation.Presented

#check OddMath.Frontier.NilCoxeterPresentation.Free
#check OddMath.Frontier.NilCoxeterPresentation.Relator
#check OddMath.Frontier.NilCoxeterPresentation.Presented
#check OddMath.Frontier.NilCoxeterPresentation.toNilHecke
#check OddMath.Frontier.NilCoxeterPresentation.toNilHecke_crossing
#check OddMath.Frontier.NilCoxeterPresentation.product
#check OddMath.Frontier.NilCoxeterPresentation.reduced_signed
#check OddMath.Frontier.NilCoxeterPresentation.nonreduced_zero
#check OddMath.Frontier.NilCoxeterPresentation.word_normalization
#check OddMath.Frontier.NilCoxeterPresentation.dividedElement_mul_additive
#check OddMath.Frontier.NilCoxeterPresentation.dividedElement_mul_nonadditive
#check OddMath.Frontier.NilCoxeterPresentation.reduced_global_sign
#check OddMath.Frontier.NilCoxeterPresentation.mem_basisSpan
#check OddMath.Frontier.NilCoxeterPresentation.basis
#check OddMath.Frontier.NilCoxeterPresentation.basis_apply
#check OddMath.Frontier.NilCoxeterPresentation.existsUnique_expansion
#check OddMath.Frontier.NilCoxeterPresentation.toNilHecke_injective
#check OddMath.Frontier.NilCoxeterPresentation.action_injective
#check OddMath.Frontier.NilCoxeterPresentation.faithful_action
#print axioms OddMath.Frontier.NilCoxeterPresentation.toNilHecke_injective
#print axioms OddMath.Frontier.NilCoxeterPresentation.basis
#print axioms OddMath.Frontier.NilCoxeterPresentation.action_injective
#print axioms OddMath.Frontier.NilCoxeterPresentation.reduced_signed
#print axioms OddMath.Frontier.NilCoxeterPresentation.mem_basisSpan

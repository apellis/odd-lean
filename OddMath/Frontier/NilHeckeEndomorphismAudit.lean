import OddMath.Frontier.NilHeckeEndomorphismControls

-- Audit every owned logical declaration, including private/generated helpers.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.NilHeckeEndomorphism,
        `OddMath.Frontier.NilHeckeEndomorphismControls].contains env.header.moduleNames[idx.toNat]!
    | none => false
  for required in [``OddMath.Frontier.NilHeckeEndomorphism.actionEquiv,
      ``OddMath.Frontier.NilHeckeEndomorphism.matrixEquiv,
      ``OddMath.Frontier.NilHeckeEndomorphism.restrictedAction_surjective,
      ``OddMath.Frontier.NilHeckeEndomorphism.coefficient_evaluation,
      ``OddMath.Frontier.NilHeckeEndomorphism.polynomial_evaluation,
      ``OddMath.Frontier.NilHeckeEndomorphismControls.arbitrary_matrix,
      ``OddMath.Frontier.NilHeckeEndomorphismControls.kernel_noncommuting] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"

#print OddMath.Frontier.NilHeckeEndomorphism.rightKernelEnd
#check OddMath.Frontier.NilHeckeEndomorphism.restrictedAction
#check OddMath.Frontier.NilHeckeEndomorphism.restrictedAction_injective
#check OddMath.Frontier.NilHeckeEndomorphism.restrictedAction_surjective
#check OddMath.Frontier.NilHeckeEndomorphism.actionEquiv
#check OddMath.Frontier.NilHeckeEndomorphism.actionEquiv_apply
#check OddMath.Frontier.NilHeckeEndomorphism.matrixEquiv
#check OddMath.Frontier.NilHeckeEndomorphism.matrixEquiv_apply
#check OddMath.Frontier.NilHeckeEndomorphism.coefficient_evaluation
#check OddMath.Frontier.NilHeckeEndomorphism.polynomial_evaluation

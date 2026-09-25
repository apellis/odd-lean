import OddMath.Frontier.NilHeckeCenterControls

-- Whole-module closure audit: safe generated helpers are NOT exempted.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.NilHeckeCenter,
        `OddMath.Frontier.NilHeckeCenterControls].contains env.header.moduleNames[idx.toNat]!
    | none => false
  for required in [``OddMath.Frontier.NilHeckeCenter.prop215_counterexample,
      ``OddMath.Frontier.NilHeckeCenter.volume_commutes,
      ``OddMath.Frontier.NilHeckeCenter.dotVolume_commutes,
      ``OddMath.Frontier.NilHeckeCenter.kernelVolume_central,
      ``OddMath.Frontier.NilHeckeCenter.squared_odd_coefficient,
      ``OddMath.Frontier.NilHeckeCenter.polynomialInclusion_action,
      ``OddMath.Frontier.NilHeckeCenter.dotVolume_not_squared_image,
      ``OddMath.Frontier.NilHeckeCenterControls.volume_not_odd_supercentral,
      ``OddMath.Frontier.NilHeckeCenterControls.source_nilHecke_claim_false,
      ``OddMath.Frontier.NilHeckeCenterControls.source_kernel_claim_false] do
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

#print OddMath.Frontier.NilHeckeCenter.volume
#print OddMath.Frontier.NilHeckeCenter.dotVolume
#print OddMath.Frontier.NilHeckeCenter.squaredVariableRing
#print OddMath.Frontier.NilHeckeCenter.squaredDotRing
#check OddMath.Frontier.NilHeckeCenter.prop215_counterexample
#check OddMath.Frontier.NilHeckeCenter.volume_commutes
#check OddMath.Frontier.NilHeckeCenter.dotVolume_commutes
#check OddMath.Frontier.NilHeckeCenter.squared_odd_coefficient
#check OddMath.Frontier.NilHeckeCenter.polynomialInclusion_action
#check OddMath.Frontier.NilHeckeCenter.kernel_center_counterexample
#check OddMath.Frontier.NilHeckeCenter.nilHecke_center_counterexample
#check OddMath.Frontier.NilHeckeCenterControls.source_first_claim_false
#check OddMath.Frontier.NilHeckeCenterControls.source_kernel_claim_false
#check OddMath.Frontier.NilHeckeCenterControls.source_nilHecke_claim_false

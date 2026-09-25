import OddMath.Frontier.NilHeckeRightBasisControls

-- Complete transitive logical-axiom audit: all declarations owned by BOTH
-- production and controls, including private and generated proof helpers.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [ `OddMath.Frontier.NilHeckeRightBasis,
        `OddMath.Frontier.NilHeckeRightBasisControls].contains env.header.moduleNames[idx.toNat]!
    | none => false
  for required in [``OddMath.Frontier.NilHeckeRightBasis.reverseFree_relator,
      ``OddMath.Frontier.NilHeckeRightBasis.reverse_involutive,
      ``OddMath.Frontier.NilHeckeRightBasis.reverse_divided_signed,
      ``OddMath.Frontier.NilHeckeRightBasis.rightSpan_eq_top,
      ``OddMath.Frontier.NilHeckeRightBasis.rightBasisElement_linearIndependent,
      ``OddMath.Frontier.NilHeckeRightBasis.basis,
      ``OddMath.Frontier.NilHeckeRightBasis.existsUnique_expansion,
      ``OddMath.Frontier.NilHeckeRightBasis.action_rightBasisElement_apply,
      ``OddMath.Frontier.NilHeckeRightBasis.rightOperator_linearIndependent,
      ``OddMath.Frontier.NilHeckeRightBasisControls.left_ne_right_nonconstant,
      ``OddMath.Frontier.NilHeckeRightBasisControls.non_self_inverse,
      ``OddMath.Frontier.NilHeckeRightBasisControls.integral_coordinates] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing production/consumer declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' unsafe={info.isUnsafe} depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"

#check OddMath.Frontier.NilHeckeRightBasis.rightBasisElement
#check OddMath.Frontier.NilHeckeRightBasis.reverseFree_relator
#check OddMath.Frontier.NilHeckeRightBasis.reverse_mul
#check OddMath.Frontier.NilHeckeRightBasis.reverse_involutive
#check OddMath.Frontier.NilHeckeRightBasis.permutation_reverse
#check OddMath.Frontier.NilHeckeRightBasis.reverse_divided_signed
#check OddMath.Frontier.NilHeckeRightBasis.reverse_dotMonomial
#check OddMath.Frontier.NilHeckeRightBasis.reverse_right_unit
#check OddMath.Frontier.NilHeckeRightBasis.rightSpan_eq_top
#check OddMath.Frontier.NilHeckeRightBasis.rightBasisElement_linearIndependent
#check OddMath.Frontier.NilHeckeRightBasis.basis
#check OddMath.Frontier.NilHeckeRightBasis.basis_apply
#check OddMath.Frontier.NilHeckeRightBasis.existsUnique_expansion
#check OddMath.Frontier.NilHeckeRightBasis.action_rightBasisElement_apply
#check OddMath.Frontier.NilHeckeRightBasis.rightOperator_linearIndependent
#check OddMath.Frontier.NilHeckeRightBasis.right_relation_coefficients
#print axioms OddMath.Frontier.NilHeckeRightBasis.basis
#print axioms OddMath.Frontier.NilHeckeRightBasis.rightOperator_linearIndependent

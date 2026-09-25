import OddMath.Frontier.EKGeneralQ
import OddMath.Frontier.EKGeneralQControls

/-!
# Axiom audit (EK §2.1 at general q)

`#print axioms` for every named owned declaration, then a meta-level sweep over EVERY
non-compiler constant (including instance/match/an unpublished script constants; compiler-internal
`_cstage`/`_spec` artifacts excluded as `Name.isInternal`) under the two owned
namespaces, failing the build if any axiom outside `propext`, `Classical.choice`,
`Quot.sound` occurs (in particular `sorryAx`).
-/

open Lean Elab Command

#print axioms OddMath.Frontier.EKGeneralQ.L
#print axioms OddMath.Frontier.EKGeneralQ.LL
#print axioms OddMath.Frontier.EKGeneralQ.h
#print axioms OddMath.Frontier.EKGeneralQ.h_zero
#print axioms OddMath.Frontier.EKGeneralQ.hWord
#print axioms OddMath.Frontier.EKGeneralQ.wordBasis
#print axioms OddMath.Frontier.EKGeneralQ.wordBasis_eq
#print axioms OddMath.Frontier.EKGeneralQ.wordBasis_one
#print axioms OddMath.Frontier.EKGeneralQ.wordBasis_mul
#print axioms OddMath.Frontier.EKGeneralQ.wordBasis_of
#print axioms OddMath.Frontier.EKGeneralQ.partWord_value
#print axioms OddMath.Frontier.EKGeneralQ.tensorBasis
#print axioms OddMath.Frontier.EKGeneralQ.tensorBasis_apply
#print axioms OddMath.Frontier.EKGeneralQ.basis_induction
#print axioms OddMath.Frontier.EKGeneralQ.tensorMulLinear
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_basis
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_zero_left
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_zero_right
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_add_left
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_add_right
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_smul_left
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_smul_right
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_hWords
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_assoc
#print axioms OddMath.Frontier.EKGeneralQ.tensorOne
#print axioms OddMath.Frontier.EKGeneralQ.tensorOne_eq
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_one_left
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_one_right
#print axioms OddMath.Frontier.EKGeneralQ.QTensor
#print axioms OddMath.Frontier.EKGeneralQ.qEquiv
#print axioms OddMath.Frontier.EKGeneralQ.generatorCoproduct
#print axioms OddMath.Frontier.EKGeneralQ.coproductAlg
#print axioms OddMath.Frontier.EKGeneralQ.coproduct
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_one
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_mul
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_h
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_two
#print axioms OddMath.Frontier.EKGeneralQ.counitAlg
#print axioms OddMath.Frontier.EKGeneralQ.counit
#print axioms OddMath.Frontier.EKGeneralQ.counit_one
#print axioms OddMath.Frontier.EKGeneralQ.counit_mul
#print axioms OddMath.Frontier.EKGeneralQ.counit_h_succ
#print axioms OddMath.Frontier.EKGeneralQ.counit_word
#print axioms OddMath.Frontier.EKGeneralQ.counit_h
#print axioms OddMath.Frontier.EKGeneralQ.leftCounit
#print axioms OddMath.Frontier.EKGeneralQ.rightCounit
#print axioms OddMath.Frontier.EKGeneralQ.leftCounit_tmul
#print axioms OddMath.Frontier.EKGeneralQ.rightCounit_tmul
#print axioms OddMath.Frontier.EKGeneralQ.leftCounit_mul
#print axioms OddMath.Frontier.EKGeneralQ.rightCounit_mul
#print axioms OddMath.Frontier.EKGeneralQ.leftCounit_coproduct_h
#print axioms OddMath.Frontier.EKGeneralQ.rightCounit_coproduct_h
#print axioms OddMath.Frontier.EKGeneralQ.counit_laws
#print axioms OddMath.Frontier.EKGeneralQ.tensorDegree
#print axioms OddMath.Frontier.EKGeneralQ.tensorDegree_basis
#print axioms OddMath.Frontier.EKGeneralQ.tensorDegree_induction
#print axioms OddMath.Frontier.EKGeneralQ.tensorDegree_mul
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_h_degree
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_word_degree
#print axioms OddMath.Frontier.EKGeneralQ.T3
#print axioms OddMath.Frontier.EKGeneralQ.tripleBasis
#print axioms OddMath.Frontier.EKGeneralQ.tripleMulLinear
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_basis
#print axioms OddMath.Frontier.EKGeneralQ.leftDelta
#print axioms OddMath.Frontier.EKGeneralQ.rightDelta
#print axioms OddMath.Frontier.EKGeneralQ.appendTensor
#print axioms OddMath.Frontier.EKGeneralQ.prependTensor
#print axioms OddMath.Frontier.EKGeneralQ.appendTensor_basis
#print axioms OddMath.Frontier.EKGeneralQ.prependTensor_basis
#print axioms OddMath.Frontier.EKGeneralQ.leftDelta_basis
#print axioms OddMath.Frontier.EKGeneralQ.rightDelta_basis
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_zero_left
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_zero_right
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_add_left
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_add_right
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_smul_left
#print axioms OddMath.Frontier.EKGeneralQ.tripleMul_smul_right
#print axioms OddMath.Frontier.EKGeneralQ.appendTensor_mul
#print axioms OddMath.Frontier.EKGeneralQ.prependTensor_mul
#print axioms OddMath.Frontier.EKGeneralQ.leftDelta_mul
#print axioms OddMath.Frontier.EKGeneralQ.rightDelta_mul
#print axioms OddMath.Frontier.EKGeneralQ.splitEquiv
#print axioms OddMath.Frontier.EKGeneralQ.split_sum
#print axioms OddMath.Frontier.EKGeneralQ.coassociativity_h
#print axioms OddMath.Frontier.EKGeneralQ.coassociativity
#print axioms OddMath.Frontier.EKGeneralQ.sourceForm
#print axioms OddMath.Frontier.EKGeneralQ.sourceFormAll
#print axioms OddMath.Frontier.EKGeneralQ.matForm
#print axioms OddMath.Frontier.EKGeneralQ.matForm_degree_mismatch
#print axioms OddMath.Frontier.EKGeneralQ.sourceForm_eq_matForm
#print axioms OddMath.Frontier.EKGeneralQ.sourceFormAll_eq_matForm
#print axioms OddMath.Frontier.EKGeneralQ.matForm_transpose
#print axioms OddMath.Frontier.EKGeneralQ.matForm_erase_zero_row
#print axioms OddMath.Frontier.EKGeneralQ.matForm_erase_zero_column
#print axioms OddMath.Frontier.EKGeneralQ.matForm_convolution
#print axioms OddMath.Frontier.EKGeneralQ.parts
#print axioms OddMath.Frontier.EKGeneralQ.vWord
#print axioms OddMath.Frontier.EKGeneralQ.form
#print axioms OddMath.Frontier.EKGeneralQ.form_basis
#print axioms OddMath.Frontier.EKGeneralQ.form_basis_mat
#print axioms OddMath.Frontier.EKGeneralQ.form_symm
#print axioms OddMath.Frontier.EKGeneralQ.vWord_nil
#print axioms OddMath.Frontier.EKGeneralQ.vWord_succ
#print axioms OddMath.Frontier.EKGeneralQ.vWord_erase_zero
#print axioms OddMath.Frontier.EKGeneralQ.vWord_parts
#print axioms OddMath.Frontier.EKGeneralQ.form_vWord_positive
#print axioms OddMath.Frontier.EKGeneralQ.form_vWord
#print axioms OddMath.Frontier.EKGeneralQ.form_hWords
#print axioms OddMath.Frontier.EKGeneralQ.tensorFormAux
#print axioms OddMath.Frontier.EKGeneralQ.tensorForm
#print axioms OddMath.Frontier.EKGeneralQ.tensorForm_tmul
#print axioms OddMath.Frontier.EKGeneralQ.tensorForm_symm
#print axioms OddMath.Frontier.EKGeneralQ.vWord_join
#print axioms OddMath.Frontier.EKGeneralQ.vWord_singleton
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_vWords
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_vWord
#print axioms OddMath.Frontier.EKGeneralQ.adjointness_vWords
#print axioms OddMath.Frontier.EKGeneralQ.adjointness_basis
#print axioms OddMath.Frontier.EKGeneralQ.adjointness
#print axioms OddMath.Frontier.EKGeneralQ.ek_sec21_general_q
#print axioms OddMath.Frontier.EKGeneralQ.h_int
#print axioms OddMath.Frontier.EKGeneralQ.tensorMul_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.coproduct_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.counit_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.matForm_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.sourceFormAll_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.form_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.tensorForm_neg_one
#print axioms OddMath.Frontier.EKGeneralQ.specialization_neg_one

#print axioms OddMath.Frontier.EKGeneralQControls.P
#print axioms OddMath.Frontier.EKGeneralQControls.padd
#print axioms OddMath.Frontier.EKGeneralQControls.pscale
#print axioms OddMath.Frontier.EKGeneralQControls.pmul
#print axioms OddMath.Frontier.EKGeneralQControls.ppow
#print axioms OddMath.Frontier.EKGeneralQControls.pnorm
#print axioms OddMath.Frontier.EKGeneralQControls.peq
#print axioms OddMath.Frontier.EKGeneralQControls.peval
#print axioms OddMath.Frontier.EKGeneralQControls.lflat
#print axioms OddMath.Frontier.EKGeneralQControls.insertAll
#print axioms OddMath.Frontier.EKGeneralQControls.perms
#print axioms OddMath.Frontier.EKGeneralQControls.blocks
#print axioms OddMath.Frontier.EKGeneralQControls.lsum
#print axioms OddMath.Frontier.EKGeneralQControls.minimalRep
#print axioms OddMath.Frontier.EKGeneralQControls.inversions
#print axioms OddMath.Frontier.EKGeneralQControls.form
#print axioms OddMath.Frontier.EKGeneralQControls.hw
#print axioms OddMath.Frontier.EKGeneralQControls.Tensor
#print axioms OddMath.Frontier.EKGeneralQControls.delta1
#print axioms OddMath.Frontier.EKGeneralQControls.tmul
#print axioms OddMath.Frontier.EKGeneralQControls.delta
#print axioms OddMath.Frontier.EKGeneralQControls.tform
#print axioms OddMath.Frontier.EKGeneralQControls.coeff2
#print axioms OddMath.Frontier.EKGeneralQControls.Tensor3
#print axioms OddMath.Frontier.EKGeneralQControls.leftDelta
#print axioms OddMath.Frontier.EKGeneralQControls.rightDelta
#print axioms OddMath.Frontier.EKGeneralQControls.coeff3
#print axioms OddMath.Frontier.EKGeneralQControls.compsF
#print axioms OddMath.Frontier.EKGeneralQControls.comps
#print axioms OddMath.Frontier.EKGeneralQControls.words3
#print axioms OddMath.Frontier.EKGeneralQControls.splits
#print axioms OddMath.Frontier.EKGeneralQControls.example_2_1
#print axioms OddMath.Frontier.EKGeneralQControls.form_h1h1
#print axioms OddMath.Frontier.EKGeneralQControls.form_h111
#print axioms OddMath.Frontier.EKGeneralQControls.symmetry_le3
#print axioms OddMath.Frontier.EKGeneralQControls.adjointness_le3
#print axioms OddMath.Frontier.EKGeneralQControls.adjointness_mismatch_le3
#print axioms OddMath.Frontier.EKGeneralQControls.counit_le3
#print axioms OddMath.Frontier.EKGeneralQControls.coassoc_le3
#print axioms OddMath.Frontier.EKGeneralQControls.coproduct_two_le2
#print axioms OddMath.Frontier.EKGeneralQControls.not_cocommutative
#print axioms OddMath.Frontier.EKGeneralQControls.form_h1h1_at_neg_one
#print axioms OddMath.Frontier.EKGeneralQControls.form_h2_at_neg_one
#print axioms OddMath.Frontier.EKGeneralQControls.integrated_h1h1
#print axioms OddMath.Frontier.EKGeneralQControls.integrated_h2

/-- Sweep every constant of the owned namespaces; error on any non-standard axiom. -/
elab "#audit_ek_general_q" : command => do
  let env ← getEnv
  let prefixes : List Name := [`OddMath.Frontier.EKGeneralQ, `OddMath.Frontier.EKGeneralQControls]
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let owned := env.constants.fold (init := #[]) fun acc c _ =>
    if !c.isInternal && prefixes.any (fun p => p.isPrefixOf c) then acc.push c else acc
  let mut bad : Array (Name × Name) := #[]
  for c in owned do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless std.contains a do bad := bad.push (c, a)
  let skipped : Nat := env.constants.fold (init := (0 : Nat)) fun n c _ =>
    if c.isInternal && prefixes.any (fun p => p.isPrefixOf c) then n + 1 else n
  logInfo m!"audited {owned.size} owned constants ({skipped} compiler-internal skipped); non-standard axioms: {bad.size}"
  unless bad.isEmpty do throwError m!"non-standard axioms: {bad}"

#audit_ek_general_q


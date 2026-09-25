import OddMath.Frontier.EKSelfTransposeControls

open scoped BigOperators
open OddMath.Frontier
open EKSelfTranspose
noncomputable section

-- The exact original types, for every n, not supplied finite families.
example (n : ℕ) : SelfTranspose n =
    {μ : DegreeShapes.DegreeShape n // μ.val.transpose = μ.val} := rfl
example (n : ℕ) : DistinctOddParts n =
    {parts : List ℕ // parts.Pairwise (· > ·) ∧
      (∀ a ∈ parts, 0 < a ∧ Odd a) ∧ parts.sum = n} := rfl
example (n : ℕ) : SelfTranspose n ≃ DistinctOddParts n := diagonalHookEquiv n
example (n : ℕ) (μ : SelfTranspose n) :
    (diagonalHookEquiv n μ).val = hooks μ.val.val := rfl
example (n : ℕ) (μ : SelfTranspose n) (i : Fin (rank μ.val.val)) :
    ((diagonalHookEquiv n μ).val)[i.val]'(by simp [diagonalHookEquiv, hooks]) =
      (hookCells μ.val.val i).card := diagonalHookEquiv_get n μ i
example (μ : YoungDiagram) (hμ : μ.transpose = μ) (i : ℕ) (hi : (i,i) ∈ μ) :
    (hookCells μ i).card = 2 * (μ.rowLen i - i) - 1 := hookCells_card_self μ hμ i hi
example (μ : YoungDiagram) (hμ : μ.transpose = μ) :
    (-1 : ℤ)^EKSemiorthogonality.ell μ =
      (-1 : ℤ)^((hooks μ).countP (fun a => a % 4 = 3)) := sign_identity μ hμ
example (n : ℕ) :
    letI := selfTransposeFintype n
    letI := distinctOddPartsFintype n
    (∏ μ : SelfTranspose n, (-1 : ℤ)^EKSemiorthogonality.ell μ.val.val) =
      ∏ p : DistinctOddParts n, (-1 : ℤ)^(p.val.countP (fun a => a % 4 = 3)) :=
  sign_product_transport n

#print axioms diagonalHookEquiv
#print axioms diagonalHookEquiv_get
#print axioms sign_identity
#print axioms sign_product_transport

-- Audit all owned safe declarations, including private/generated declarations.
-- Unsafe compiler stages are classified separately, never treated as logical proofs.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKSelfTranspose,
        `OddMath.Frontier.EKSelfTransposeControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``SelfTranspose, ``DistinctOddParts, ``Frame.diagram,
      ``Frame.lower, ``Frame.mem_diagram, ``Frame.transpose, ``Frame.rowLen,
      ``diagonal_iff, ``frameOf_diagram, ``hooks, ``hooks_get, ``hooks_descending,
      ``hooks_positive_odd, ``hookCells_eq, ``hookCells_card_self, ``hooks_sum,
      ``ofParts, ``ofParts_self, ``hooks_ofParts, ``hooks_injective, ``ofParts_hooks,
      ``diagonalHookEquiv, ``diagonalHookEquiv_get, ``ell_card, ``crossFlip_mem,
      ``fixed_crossings, ``ell_sign_upper, ``hooks_half_sum, ``list_half_sign,
      ``sign_identity, ``selfTransposeFintype, ``distinctOddPartsFintype,
      ``sign_product_transport, ``EKSelfTransposeControls.empty_control,
      ``EKSelfTransposeControls.one_control, ``EKSelfTransposeControls.hook_three_control,
      ``EKSelfTransposeControls.hook_three_one_control, ``EKSelfTransposeControls.signs,
      ``EKSelfTransposeControls.production_hooks, ``EKSelfTransposeControls.inverse_three,
      ``EKSelfTransposeControls.inverse_three_one, ``EKSelfTransposeControls.forward_empty,
      ``EKSelfTransposeControls.forward_one, ``EKSelfTransposeControls.arbitrary_sign_consumer] do
    unless owned.any (fun (name, _) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if info.isUnsafe && compiler then
      stages := stages + 1
      Lean.logInfo m!"UNSAFE_COMPILER '{name}' depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} unsafe-compiler-stages={stages}"

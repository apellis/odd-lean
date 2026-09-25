import OddMath.Frontier.EKDeterminant

noncomputable section
open scoped BigOperators
open OddMath.Frontier
open DegreeShapes EKDualBases EKDeterminant
local instance : DecidableEq YoungDiagram := Classical.decEq _
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

-- Literal frozen source type: neither a surrogate nor a one-sided reindex.
example (d : ℕ) (μ ν : DegreeShape d) : M d μ ν =
    EKRadicalQuotient.quotientPairing (EKPartitionSpanning.ePartition μ.val)
      (EKPartitionSpanning.hPartition ν.val) := rfl
example (d : ℕ) : sourceRHS d =
    ∏ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val),
      (-1 : ℤ)^EKSemiorthogonality.ell μ.val := rfl
example : (M 2).det = -1 ∧ sourceRHS 2 = 1 := ⟨degree_two_det, degree_two_rhs⟩
example : ¬ ∀ d : ℕ, (M d).det = sourceRHS d := equation_3_4_not_all_degrees
example {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ DegreeShape 2) :
    ((M 2).submatrix e e).det ≠ sourceRHS 2 := (counterexample_under_every_order e).2
example : (M 0).det = sourceRHS 0 := degree_zero_control.1.trans degree_zero_control.2.symm
example : (M 1).det = sourceRHS 1 := degree_one_control.1.trans degree_one_control.2.symm
example : (triangularMatrix 2).det ≠ (M 2).det := one_sided_not_M_det

#print axioms equation_3_4_counterexample
#print axioms counterexample_under_every_order

-- Includes private and generated safe declarations in all three owned modules.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKDeterminant,
        `OddMath.Frontier.EKDeterminantControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``sourceRHS, ``degreeTwoEquiv, ``degree_two_matrix, ``degree_two_det,
      ``degree_two_filter, ``degree_two_rhs, ``equation_3_4_counterexample,
      ``equation_3_4_not_all_degrees, ``simultaneous_reindex_invariant,
      ``counterexample_under_every_order, ``degree_two_triangular_det,
      ``one_sided_not_M_det, ``degree_zero_control, ``degree_one_control,
      ``EKDeterminantControls.zero_matrix, ``EKDeterminantControls.one_matrix,
      ``EKDeterminantControls.two_matrix, ``EKDeterminantControls.two_no_self,
      ``EKDeterminantControls.one_sided_matrix, ``EKDeterminantControls.raw_sign_control] do
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

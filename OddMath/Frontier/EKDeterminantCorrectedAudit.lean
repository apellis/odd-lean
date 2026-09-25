import OddMath.Frontier.EKDeterminantCorrected

noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKDeterminantCorrectedAudit
open OddMath.Frontier
open DegreeShapes EKDualBases EKDeterminant EKDeterminantCorrected
local instance : DecidableEq YoungDiagram := Classical.decEq _
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

-- Literal frozen source matrix: the exhaustive index on BOTH sides, (e_ν, h_μ).
example (d : ℕ) (μ ν : DegreeShape d) : M d μ ν =
    EKRadicalQuotient.quotientPairing (EKPartitionSpanning.ePartition μ.val)
      (EKPartitionSpanning.hPartition ν.val) := rfl
-- Printed RHS is unchanged (frozen); the correction is a separate factor.
example (d : ℕ) : sourceRHS d =
    ∏ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val),
      (-1 : ℤ)^EKSemiorthogonality.ell μ.val := rfl
example (d : ℕ) : correctedRHS d =
    (-1 : ℤ)^((Fintype.card (DegreeShape d) -
      (Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val)).card)/2) *
      sourceRHS d := rfl

-- Main theorem, every d, including 0 and 1.
example : ∀ d : ℕ, (M d).det = correctedRHS d := corrected_equation_3_4
example (d : ℕ) : (M d).det = sourceRHS d * (-1 : ℤ)^((p d - sc d)/2) :=
  (corrected_equation_3_4 d).trans (corrected_eq_source_mul d)
example (d : ℕ) : (M d).det = sourceRHS d ↔ Even ((p d - sc d)/2) := printed_iff d
example (d : ℕ) : Even (p d - sc d) := p_sub_sc_even d
-- Consumer consistency with the independent degree-two computation.
example : (M 2).det = -1 ∧ correctedRHS 2 = -1 ∧ (M 2).det ≠ sourceRHS 2 :=
  ⟨degree_two_det, degree_two_direct, equation_3_4_counterexample⟩
-- Simultaneous reindexing is harmless for the corrected formula too.
example (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ DegreeShape d) :
    ((M d).submatrix e e).det = correctedRHS d := by
  rw [simultaneous_reindex_invariant, corrected_equation_3_4]

-- Frozen statement shape, no residual hypotheses.
example (d : ℕ) : (EKDualBases.M d).det = EKDeterminantCorrected.F d := det_M d
example (d : ℕ) : EKDeterminantCorrected.F d =
    (-1 : ℤ)^((Fintype.card (DegreeShape d) -
      (Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val)).card)/2) *
    ∏ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val),
      (-1 : ℤ)^EKSemiorthogonality.ell μ.val := rfl
example : EKDeterminantCorrected.F 2 = -1 ∧ EKDeterminantCorrected.F 2 = (M 2).det :=
  ⟨F_two, F_two_agrees⟩
example (d : ℕ) : EKDeterminantCorrected.F d = sourceRHS d * (-1 : ℤ)^((p d - sc d)/2) :=
  F_eq_source_mul d

#print axioms det_M
#print axioms F_two
#print axioms F_two_agrees
#print axioms F_eq_source_mul
#print axioms corrected_equation_3_4
#print axioms corrected_equation_3_4_explicit
#print axioms corrected_eq_source_mul
#print axioms EKDeterminantCorrected.degree_two
#print axioms p_sub_sc_even
#print axioms prod_all_eq_sourceRHS
#print axioms M_eq_triangular_reindex
#print axioms triangular_det
#print axioms printed_iff
#print axioms sign_involution

-- Includes private and generated declarations in both owned modules.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKDeterminantCorrected,
        `OddMath.Frontier.EKDeterminantCorrectedControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``p, ``sc, ``correctedRHS, ``M_eq_triangular_reindex, ``triangular_det,
      ``sign_involution, ``transposeShape_involutive, ``transposeShape_fixed_card,
      ``sign_transposeShape, ``p_sub_sc_even, ``prod_all_eq_sourceRHS, ``det_M_sign_prod,
      ``corrected_equation_3_4, ``corrected_equation_3_4_explicit, ``corrected_eq_source_mul,
      ``sourceRHS_sq, ``printed_iff, ``EKDeterminantCorrected.degree_two, ``degree_two_stats,
      ``degree_two_direct, ``EKDeterminantCorrected.F, ``det_M, ``F_two, ``F_two_agrees,
      ``F_eq_source_mul,
      ``EKDeterminantCorrectedControls.toy_one_fixed, ``EKDeterminantCorrectedControls.toy_two_cycles,
      ``EKDeterminantCorrectedControls.toy_halving, ``EKDeterminantCorrectedControls.degree_two_card,
      ``EKDeterminantCorrectedControls.degree_two_sc,
      ``EKDeterminantCorrectedControls.degree_two_target] do
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

end OddMath.Frontier.EKDeterminantCorrectedAudit

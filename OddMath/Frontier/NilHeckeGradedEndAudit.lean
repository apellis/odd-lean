import OddMath.Frontier.NilHeckeGradedEndControls

open OddMath.Frontier OddMath.SkewPolynomial
open NilHeckeAction NilCoxeterWords OddSchubertAction NilHeckeEndomorphism NilHeckeGradedEnd
open scoped BigOperators
noncomputable section

-- Actual source carriers, grading definitions and inherited maps.
example (n : ℕ) : Presented n = (Free n ⧸ relIdeal n) := rfl
example (N : ℕ) (d : ℤ) (f : SkewPolynomial N) :
    f ∈ polynomialPiece N d ↔ ∀ A : Fin N → ℕ,
      2*((∑ i, A i : ℕ) : ℤ) ≠ d → f A = 0 := Iff.rfl
example (n : ℕ) (d : ℤ) (k : K n) :
    k ∈ kernelPiece n d ↔ (k : SkewPolynomial (n+2)) ∈ polynomialPiece (n+2) d := Iff.rfl
example (n : ℕ) (a : Presented n) (d : ℤ) :
    a ∈ NilHeckeGrading.degreePiece n d ↔
      ∀ e : ℤ, ∀ f : SkewPolynomial (n+2), f ∈ polynomialPiece (n+2) e →
        (actionEquiv n a).val f ∈ polynomialPiece (n+2) (e+d) := actionEquiv_degree_iff n a d
example (n : ℕ) (T : rightKernelEnd n) (d : ℤ) :
    (∀ e : ℤ, ∀ f : SkewPolynomial (n+2), f ∈ polynomialPiece (n+2) e →
      T.val f ∈ polynomialPiece (n+2) (e+d)) ↔
    ∀ i j, (matrixEquiv n T i j : SkewPolynomial (n+2)) ∈
      polynomialPiece (n+2) (d+2*(length j : ℤ)-2*(length i : ℤ)) := matrixEquiv_degree_iff n T d
example (n : ℕ) (d : ℤ) (f : SkewPolynomial (n+2)) :
    f ∈ polynomialPiece (n+2) d ↔
      ∀ i, coordinates n f i ∈ kernelPiece n (d-2*(length i : ℤ)) := coordinates_degree_iff n d f
example (n : ℕ) (w : Perm n) :
    schubert w ∈ polynomialPiece (n+2) (2*(length w : ℤ)) := schubert_mem w
example (n : ℕ) : schubertRankPolynomial n =
    ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), (Polynomial.X : Polynomial ℤ)^k :=
  schubert_rank_polynomial n

#check polynomialPiece
#check kernelPiece
#check endDegree
#check matrixDegree
#check schubert_mem
#check left_homogeneous_basis
#check right_homogeneous_basis
#check coordinates_degree_iff
#check actionEquiv_degree_iff
#check matrixEquiv_degree_iff
#check graded_matrix_corollary
#check actionPieceEquiv
#check matrixPieceEquiv
#check schubert_rank_polynomial
#check schubert_physical_rank
#print axioms actionEquiv_degree_iff
#print axioms matrixEquiv_degree_iff
#print axioms coordinates_degree_iff

-- Scan every owned safe declaration (including compiler-named safe helpers).
-- Individually separate only compiler-NAMED AND unsafe generated artifacts.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.NilHeckeGradedEnd,
        `OddMath.Frontier.NilHeckeGradedEndControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``polynomialPiece, ``kernelPiece, ``endDegree, ``matrixDegree,
      ``monomial_mem, ``polynomial_negative, ``polynomial_odd, ``kernel_negative, ``kernel_odd, ``polynomial_mul,
      ``divided_mem, ``schubert_mem, ``interpolate_degree,
      ``coordinates_mem, ``coordinates_degree_iff, ``actionEquiv_degree_iff,
      ``matrixEquiv_degree_iff, ``graded_matrix_corollary, ``left_homogeneous_basis,
      ``right_homogeneous_basis, ``actionPieceEquiv, ``matrixPieceEquiv,
      ``schubertRankPolynomial, ``schubert_rank_polynomial, ``schubert_physical_rank,
      ``NilHeckeGradedEndControls.rankTwo_dot,
      ``NilHeckeGradedEndControls.homogeneous_vector_consumer,
      ``NilHeckeGradedEndControls.identity_degree,
      ``NilHeckeGradedEndControls.identity_matrix_degree,
      ``NilHeckeGradedEndControls.rankTwo_negative,
      ``NilHeckeGradedEndControls.crossing_wrong_positive,
      ``NilHeckeGradedEndControls.zero_negative,
      ``NilHeckeGradedEndControls.odd_zero,
      ``NilHeckeGradedEndControls.inhomogeneous_not_pure,
      ``NilHeckeGradedEndControls.inhomogeneous_inverse,
      ``NilHeckeGradedEndControls.raisingMatrix_degree,
      ``NilHeckeGradedEndControls.reversed_shift_rejected,
      ``NilHeckeGradedEndControls.arbitrary_source,
      ``NilHeckeGradedEndControls.arbitrary_matrix] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compilerName := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compilerName && info.isUnsafe then
      stages := stages+1
      Lean.logInfo m!"COMPILER '{name}' depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard axiom closure for {name}: {axioms.toList}"
      logical := logical+1
      Lean.logInfo m!"SAFE '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT safe={logical} compilerUnsafe={stages}"

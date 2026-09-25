import OddMath.Frontier.NilHeckeGradingControls

open OddMath.Frontier
open NilHeckeAction NilCoxeterWords NilHeckeGrading
open scoped BigOperators
noncomputable section

-- The two actual carriers and literal word-image definitions, not surrogates.
example (n : ℕ) : Presented n = (Free n ⧸ relIdeal n) := rfl
example (n : ℕ) : ONC.Q n =
    (NilCoxeterPresentation.Free n ⧸ NilCoxeterPresentation.relIdeal n) := rfl
example (n : ℕ) (d : ℤ) : degreePiece n d = Submodule.span ℤ
    (wordValue '' {w : List (Letter n) | wordDegree w=d}) := rfl
example (n : ℕ) (w : List (Letter n)) : wordValue w =
    NilHeckeBasis.quotientMap n ((w.map (FreeAlgebra.ι ℤ)).prod) := wordValue_eq_image w
example (n : ℕ) (d : ℤ) : ONC.degreePiece n d = Submodule.span ℤ
    (NilCoxeterPresentation.product '' {w : Word n | -2*(w.length : ℤ)=d}) := rfl
example (n : ℕ) (d : ℤ) : degreePiece n d = leftPiece n d := degreePiece_eq_leftPiece n d
example (n : ℕ) (d : ℤ) : degreePiece n d = rightPiece n d := degreePiece_eq_rightPiece n d
example (n : ℕ) (d : ℤ) : ONC.degreePiece n d = ONC.basisPiece n d := ONC.degreePiece_eq_basisPiece n d
example (n : ℕ) (d : ℤ) : Basis (DegreeIndex n d) ℤ (degreePiece n d) := degreeLeftBasis n d
example (n : ℕ) (d : ℤ) : Basis (DegreeIndex n d) ℤ (degreePiece n d) := degreeRightBasis n d
example (n : ℕ) (d : ℤ) : Basis (ONC.DegreeIndex n d) ℤ (ONC.degreePiece n d) := ONC.degreeBasis n d
example (n : ℕ) (d : ℤ) (w : ONC.DegreeIndex n d) :
    (ONC.degreeBasis n d w : ONC.Q n)=NilCoxeterPresentation.dividedElement w.val := ONC.degreeBasis_apply d w
example (n : ℕ) (d : ℤ) : Module.Free ℤ (degreePiece n d) := inferInstance
example (n : ℕ) (d : ℤ) : Module.Finite ℤ (degreePiece n d) := inferInstance
example (n : ℕ) (d : ℤ) : Module.Free ℤ (ONC.degreePiece n d) := inferInstance
example (n : ℕ) (d : ℤ) : Module.Finite ℤ (ONC.degreePiece n d) := inferInstance
example (n : ℕ) (x : ONC.Q n) :
    ∃! f : ℤ →₀ ONC.Q n, (∀ d, f d ∈ ONC.degreePiece n d) ∧ f.sum (fun _ y => y)=x :=
  ONC.unique_homogeneous_decomposition x
example (n : ℕ) (d : ℤ) : Module.finrank ℤ (ONC.degreePiece n d)=
    Nat.card {w : Perm n // -2*(length w : ℤ)=d} := ONC.degree_finrank n d
example (n : ℕ) : (∑ w : Perm n, (Polynomial.X : Polynomial ℤ)^length w) =
    ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), Polynomial.X^k :=
  ONC.inversion_generating_polynomial n
example (n : ℕ) (d : ℤ) : Module.finrank ℤ (degreePiece n d) =
    ∑ w : Perm n, if 0 ≤ d+2*(length w : ℤ) ∧ (d+2*(length w : ℤ))%2=0 then
      (((d+2*(length w : ℤ))/2).toNat+n+1).choose (n+1) else 0 :=
  degree_finrank_binomial n d

#check ONC.q_rank_numerator
#check ONC.q_rank_shifted_factorial
#check degree_finrank_binomial
#check degreePiece_mul
#check unique_homogeneous_decomposition
#print axioms degree_finrank_binomial
#print axioms ONC.inversion_generating_polynomial
#print axioms ONC.q_rank_shifted_factorial
#print axioms degreePiece_eq_leftPiece
#print axioms degreePiece_eq_rightPiece
#print axioms unique_homogeneous_decomposition
#print axioms ONC.unique_homogeneous_decomposition

-- All owned safe logical definitions, including private/generated helpers.
-- Only compiler-NAMED AND unsafe artifacts are segregated, never safe helpers.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.NilHeckeGrading,
        `OddMath.Frontier.NilHeckeGradingControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``wordValue_eq_image, ``degreePiece, ``degreePiece_mul, ``unit_mem,
      ``degreePiece_eq_leftPiece, ``degreePiece_eq_rightPiece,
      ``degreeLeftBasis, ``degreeRightBasis, ``degreeLeftBasis_apply, ``degreeRightBasis_apply,
      ``degree_free, ``degree_finite, ``unique_homogeneous_decomposition,
      ``degree_finrank_coefficient, ``degree_finrank_binomial, ``exponentFiber_card,
      ``exponent_sum_card, ``ONC.degreePiece, ``ONC.degreePiece_eq_basisPiece,
      ``ONC.degreePiece_mul, ``ONC.unit_mem, ``ONC.degreeBasis, ``ONC.degreeBasis_apply,
      ``ONC.degree_free, ``ONC.degree_finite, ``ONC.unique_homogeneous_decomposition,
      ``ONC.degree_finrank, ``ONC.inversion_generating_polynomial,
      ``ONC.q_rank_numerator, ``ONC.q_rank_shifted_factorial, ``ONC.evalWord_eq_image,
      ``NilHeckeGradingControls.rankTwo_ONC_rank_negative,
      ``NilHeckeGradingControls.rankTwo_ONC_rank_zero,
      ``NilHeckeGradingControls.rankTwo_ONC_rank_below,
      ``NilHeckeGradingControls.negative_degree,
      ``NilHeckeGradingControls.wrong_positive_degree_rejected,
      ``NilHeckeGradingControls.odd_zero, ``NilHeckeGradingControls.unit_control,
      ``NilHeckeGradingControls.rankTwo_rank_negative,
      ``NilHeckeGradingControls.rankTwo_rank_zero,
      ``NilHeckeGradingControls.rankTwo_rank_two,
      ``NilHeckeGradingControls.rankTwo_rank_below,
      ``NilHeckeGradingControls.arbitrary_homogeneous_product,
      ``NilHeckeGradingControls.arbitrary_ONC_product] do
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
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical+1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"

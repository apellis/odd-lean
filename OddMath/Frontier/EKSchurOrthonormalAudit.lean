import OddMath.Frontier.EKSchurOrthonormalControls
import OddMath.Frontier.EKSchurOrthonormal

open scoped BigOperators
open OddMath.Frontier
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKSchurOrthonormal EKSchurOrthonormalControls
open EKPartitionSpanning (hPartition)
noncomputable section
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! Exact type boundary: every object below is the inherited, unmodified one. -/

-- The quotient, the pairing, the degree piece and the bases are the existing ones.
example : Q = ((FreeAlgebra ℤ ℕ) ⧸ radical) := rfl
example (d : ℕ) : Basis (DegreeShape d) ℤ (degreePiece d) := mBasis d
example (d : ℕ) (ν : DegreeShape d) : (degreeHBasis d ν : Q) = hPartition ν.val :=
  degreeHBasis_apply d ν
-- Source M′ = (h,h) is `Mh`, NOT the (e,h) matrix `M`.
example (d : ℕ) (ν μ : DegreeShape d) :
    Mh d ν μ = quotientPairing (hPartition ν.val) (hPartition μ.val) := rfl
-- K is the literal (3.7) normalized signed tableau count.
example (lam mu : YoungDiagram) : signedKostka lam mu =
    tableauSign (canonicalTableau lam) *
      ∑ T ∈ TableauContent.tableauxOfContent lam (shapeContent mu), tableauSign T := rfl
-- s_λ is the inherited (3.6) inversion applied to the actual h-basis.
example (d : ℕ) : schur d = KostkaModuleInversion.recover d (degreeHBasis d) := rfl
-- The sign statistics are literal: λ₂ + λ₄ + … and Σ_j C(λᵀ_j, 2) on Mathlib's transpose.
example (a b c e f : ℕ) : evenParts [a, b, c, e, f] = b + e := by
  simp [evenParts, Finset.sum_range_succ]
example (μ : YoungDiagram) :
    transposeChoose μ = (μ.transpose.rowLens.map (fun a => a.choose 2)).sum := rfl

-- The hypothesis is EXACTLY (3.9) in the single degree d.
example (d : ℕ) : Identity39 d ↔ ∀ μ ρ : DegreeShape d, Mh d μ ρ = ∑ lam : DegreeShape d,
    (-1 : ℤ) ^ evenParts lam.val.rowLens * signedKostka lam.val μ.val *
      signedKostka lam.val ρ.val := Iff.rfl

-- (3.6), (3.10), (3.11) with their exact statements.
example (d : ℕ) (μ : DegreeShape d) :
    degreeHBasis d μ = ∑ lam, signedKostka lam.val μ.val • schur d lam := schur_defining d μ
example (d : ℕ) (h39 : Identity39 d) (lam : DegreeShape d) :
    (-1 : ℤ) ^ transposeChoose lam.val • schur d lam =
      ∑ μ, signedKostka lam.val μ.val • mBasis d μ := corollary_3_8 d h39 lam
example (d : ℕ) (h39 : Identity39 d) (lam μ : DegreeShape d) :
    quotientPairing (schur d lam : Q) (schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := corollary_3_9 d h39 lam μ
example (μ : YoungDiagram) : (-1 : ℤ) ^ transposeChoose μ = (-1 : ℤ) ^ evenParts μ.rowLens :=
  sign_bridge μ

-- Non-vacuity: the hypothesis actually holds (by computation) in degrees 0–4, so the
-- unconditional corollaries there are genuine, not ex falso.
example : Identity39 4 := identity39_le_four 4 le_rfl
example (lam μ : DegreeShape 4) :
    quotientPairing (schur 4 lam : Q) (schur 4 μ : Q) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 :=
  corollary_3_9_le_four 4 le_rfl lam μ
-- The form is signed, not positive definite: s_(1,1) has norm -1.
example : quotientPairing (schur 2 sh11 : Q) (schur 2 sh11 : Q) = -1 :=
  degree_two_schur_norms.2.1

#check @schur_defining
#check @schur_val_unique
#check @corollary_3_8
#check @corollary_3_9
#check @sign_bridge
#check @identity39_le_four
#check @corollary_3_8_le_four
#check @corollary_3_9_le_four
#check @EKSchurOrthonormalControls.Mh_eq_PL
#check @EKSchurOrthonormalControls.signedKostka_eq_KW
#check @EKSchurOrthonormalControls.pairing_eq_P
#print axioms corollary_3_8
#print axioms corollary_3_9
#print axioms sign_bridge
#print axioms corollary_3_8_le_four
#print axioms corollary_3_9_le_four
#print axioms EKSchurOrthonormalControls.identity39_4
#print axioms EKSchurOrthonormalControls.signedKostka_eq_KW
#print axioms EKSchurOrthonormalControls.Mh_eq_PL

-- All safe declarations in the owned modules, including private/generated helpers, must
-- have only standard transitive axioms. ONLY unsafe compiler stages are separated.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKSchurOrthonormal,
        `OddMath.Frontier.EKSchurOrthonormalControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``schur, ``schur_defining, ``schur_val_unique, ``Identity39,
      ``corollary_3_8, ``corollary_3_9, ``sign_bridge, ``transposeChoose_eq,
      ``cells_fst_sum_cols, ``cells_fst_sum_rows, ``evenParts_rowLens,
      ``identity39_le_four, ``corollary_3_8_le_four, ``corollary_3_9_le_four,
      ``schur_hand1, ``schur_hand2, ``schur_hand3, ``degree_two_schur_norms,
      ``EKSchurOrthonormalControls.evenParts, ``EKSchurOrthonormalControls.transposeChoose,
      ``EKSchurOrthonormalControls.pairing_eq_P, ``EKSchurOrthonormalControls.Mh_eq_PL,
      ``EKSchurOrthonormalControls.signedKostka_eq_KW, ``EKSchurOrthonormalControls.rowCells_eq_of,
      ``EKSchurOrthonormalControls.small_partition, ``EKSchurOrthonormalControls.exhaust4,
      ``EKSchurOrthonormalControls.identity39_0, ``EKSchurOrthonormalControls.identity39_1,
      ``EKSchurOrthonormalControls.identity39_2, ``EKSchurOrthonormalControls.identity39_3,
      ``EKSchurOrthonormalControls.identity39_4,
      ``EKSchurOrthonormalControls.bridge_matches_inherited_degree_two,
      ``EKSchurOrthonormalControls.hand_values, ``EKSchurOrthonormalControls.hand1_defining,
      ``EKSchurOrthonormalControls.hand2_defining, ``EKSchurOrthonormalControls.hand3_defining,
      ``EKSchurOrthonormalControls.hand1_gram, ``EKSchurOrthonormalControls.hand2_gram,
      ``EKSchurOrthonormalControls.hand3_gram, ``EKSchurOrthonormalControls.sign_fixture,
      ``EKSchurOrthonormalControls.degree_two_norms,
      ``EKSchurOrthonormalControls.unsigned_rejected,
      ``EKSchurOrthonormalControls.odd_parts_rejected,
      ``EKSchurOrthonormalControls.eh_matrix_rejected,
      ``EKSchurOrthonormalControls.transposed_kostka_rejected,
      ``EKSchurOrthonormalControls.statistics_differ,
      ``EKSchurOrthonormalControls.example_3_5, ``EKSchurOrthonormalControls.example_3_6] do
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

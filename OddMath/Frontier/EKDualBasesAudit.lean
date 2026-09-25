import OddMath.Frontier.EKDualBasesControls

open scoped BigOperators
open OddMath.Frontier
open EKRadicalQuotient EKIntegralBases EKDualBases
noncomputable section
local instance (d : ℕ) : Fintype (DegreeShapes.DegreeShape d) := DegreeShapes.degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShapes.DegreeShape d) := Classical.decEq _

-- Exact type boundary, no supplied perfectness or nonzero-degree hypothesis.
example : Q = ((FreeAlgebra ℤ ℕ) ⧸ radical) := rfl
example (d : ℕ) : degreePiece d ≃ₗ[ℤ] Module.Dual ℤ (degreePiece d) := pairingEquiv d
example (d : ℕ) (x y : degreePiece d) :
    pairingEquiv d x y = quotientPairing y.val x.val := rfl
example (d : ℕ) : Basis (DegreeShapes.DegreeShape d) ℤ (degreePiece d) := mBasis d
example (d : ℕ) : Basis (DegreeShapes.DegreeShape d) ℤ (degreePiece d) := fBasis d
example (d : ℕ) (l : Module.Dual ℤ (degreePiece d)) :
    ∃! x : degreePiece d, ∀ y : degreePiece d, quotientPairing y.val x.val = l y :=
  unique_representative d l
example (d : ℕ) (x : degreePiece d) :
    x = ∑ μ, quotientPairing (EKPartitionSpanning.ePartition μ.val) x.val • fBasis d μ :=
  reconstruct_f d x

#check pairingEquiv
#check mBasis
#check fBasis
#check h_m
#check e_f
#check m_unique
#check f_unique
#check m_coordinates
#check f_coordinates
#check reconstruct_m
#check reconstruct_f
#check h_eq_M_f
#check h_eq_Mh_m
#check e_eq_M_m
#check e_eq_Me_f
#check M_det_unit
#check Mh_det_unit
#check Me_det_unit
#check proposition_3_1_M
#check proposition_3_1_Mh
#check proposition_3_1_Me
#print axioms pairingEquiv
#print axioms proposition_3_1_M
#print axioms proposition_3_1_Mh
#print axioms proposition_3_1_Me

-- All safe declarations in the owned modules, including private/generated
-- helpers, must have only standard transitive axioms. ONLY unsafe compiler
-- stages are separated; a safe compiler-named declaration is still audited.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKDualBases,
        `OddMath.Frontier.EKDualBasesControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``pairingMap, ``triangularMatrix_det_unit, ``pairingInverse_left,
      ``pairingInverse_right, ``pairingEquiv, ``unique_representative, ``mBasis, ``fBasis,
      ``h_m, ``e_f, ``m_unique, ``f_unique, ``m_coordinates, ``f_coordinates,
      ``reconstruct_m, ``reconstruct_f, ``M, ``Mh, ``Me, ``M_symm, ``Mh_symm, ``Me_symm,
      ``h_eq_M_f, ``h_eq_Mh_m, ``e_eq_M_m, ``e_eq_Me_f,
      ``M_det_unit, ``Mh_det_unit, ``Me_det_unit,
      ``proposition_3_1_M, ``proposition_3_1_Mh, ``proposition_3_1_Me,
      ``crossing_source_transpose, ``cable_transpose,
      ``EKDualBasesControls.empty_pairing, ``EKDualBasesControls.degree_one,
      ``EKDualBasesControls.degree_two_gram, ``EKDualBasesControls.empty_dual_unit,
      ``EKDualBasesControls.degree_two_duals, ``EKDualBasesControls.arbitrary_degree_consumer,
      ``EKDualBasesControls.cable_sign_required, ``EKDualBasesControls.wrong_m_row2_rejected,
      ``EKDualBasesControls.southwest_northeast_sign_control] do
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

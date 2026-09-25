import OddMath.Frontier.EKIntegralBasesControls

open scoped BigOperators
open OddMath.Frontier
open EKRadicalQuotient EKIntegralBases

-- Exact carrier, degree source, literal partition vectors and all parameters.
example : Q = ((FreeAlgebra ℤ ℕ) ⧸ radical) := rfl
example (d : ℕ) : degreePiece d = Submodule.span ℤ
    (Set.range (fun w : {w : EKFreeCoproduct.W // EKFreeCoproduct.degree w = d} =>
      pi (EKFreeCoproduct.wordBasis w.val))) := rfl
example (μ : YoungDiagram) : hBasis μ = (μ.rowLens.map EKElementaryQuotient.h).prod :=
  hBasis_apply μ
example (μ : YoungDiagram) : eBasis μ = (μ.rowLens.map EKElementaryQuotient.e).prod :=
  eBasis_apply μ
example (d : ℕ) : degreePiece d = Submodule.span ℤ
    (Set.range (fun μ : DegreeShapes.DegreeShape d => EKPartitionSpanning.hPartition μ.val)) :=
  degreePiece_eq_hPartition_span d
example (d : ℕ) : degreePiece d = Submodule.span ℤ
    (Set.range (fun μ : DegreeShapes.DegreeShape d => EKPartitionSpanning.ePartition μ.val)) :=
  degreePiece_eq_ePartition_span d
example (d : ℕ) (μ : DegreeShapes.DegreeShape d) :
    (degreeHBasis d μ : Q) = (μ.val.rowLens.map EKElementaryQuotient.h).prod :=
  degreeHBasis_apply d μ
example (d : ℕ) (μ : DegreeShapes.DegreeShape d) :
    (degreeEBasis d μ : Q) = (μ.val.rowLens.map EKElementaryQuotient.e).prod :=
  degreeEBasis_apply d μ
example (d : ℕ) : Module.Free ℤ (degreePiece d) := inferInstance
example (d : ℕ) : Module.Finite ℤ (degreePiece d) := inferInstance
example (d : ℕ) :
    letI := DegreeShapes.degreeFintype d
    Module.finrank ℤ (degreePiece d) = Fintype.card (DegreeShapes.DegreeShape d) :=
  degree_finrank d
example (a b : ℕ) (x : degreePiece a) (y : degreePiece b) :
    (x : Q) * (y : Q) ∈ degreePiece (a+b) := degreePiece_mul x.property y.property
example (x : Q) :
    ∃! f : ℕ →₀ Q, (∀ d, f d ∈ degreePiece d) ∧ f.sum (fun _ y => y) = x :=
  unique_homogeneous_decomposition x

#check hBasis
#check eBasis
#check h_unique_coordinates
#check e_unique_coordinates
#check degreePiece
#check degreePiece_eq_hPartition_span
#check degreePiece_eq_ePartition_span
#check degreeHBasis
#check degreeEBasis
#check degree_h_unique_coordinates
#check degree_e_unique_coordinates
#check degree_finrank
#check degreePiece_mul
#check unique_homogeneous_decomposition
#check degree_disjoint
#check unit_mem_degree_zero
#print axioms hBasis
#print axioms eBasis
#print axioms degreeHBasis
#print axioms degreeEBasis
#print axioms degree_finrank
#print axioms degreePiece_mul
#print axioms unique_homogeneous_decomposition

-- Complete transitive closure, including private and generated logical helpers.
-- Unsafe compiler stages are logged separately and never admitted as proofs.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKIntegralBases,
        `OddMath.Frontier.EKIntegralBasesControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``hBasis, ``eBasis, ``hBasis_apply, ``eBasis_apply,
      ``h_unique_coordinates, ``e_unique_coordinates,
      ``degreePiece, ``degreePiece_eq_hPartition_span, ``degreePiece_eq_ePartition_span,
      ``degreeHBasis, ``degreeEBasis, ``degreeHBasis_apply, ``degreeEBasis_apply,
      ``degree_free, ``degree_finite, ``degree_finrank,
      ``degree_h_unique_coordinates, ``degree_e_unique_coordinates,
      ``degreePiece_mul, ``unique_homogeneous_decomposition, ``degree_disjoint,
      ``unit_mem_degree_zero, ``decompose_unit,
      ``EKIntegralBasesControls.degree_two_coordinates,
      ``EKIntegralBasesControls.degree_three_coordinates,
      ``EKIntegralBasesControls.wrong_elementary_sign_rejected,
      ``EKIntegralBasesControls.wrong_degree_three_swap_rejected,
      ``EKIntegralBasesControls.inhomogeneous_control,
      ``EKIntegralBasesControls.arbitrary_degree_consumer] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"

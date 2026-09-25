import OddMath.Frontier.EKTriangularControls

noncomputable section
open scoped BigOperators
open OddMath.Frontier EKRadicalQuotient EKElementaryQuotient
open EKIntegralBases EKPartitionSpanning EKAutomorphisms EKTriangular

namespace OddMath.Frontier.EKTriangularAudit

example : Q = (CompleteElementary.A ⧸ EKRadicalQuotient.radical) := rfl
example (μ : YoungDiagram) : hPartition μ=(μ.rowLens.map h).prod := rfl
example (μ : YoungDiagram) : b μ=(μ.rowLens.map (fun n => n.choose 2)).sum := rfl
example (μ : YoungDiagram) : Hge μ=Submodule.span ℤ
    {x | ∃ ν : YoungDiagram, ν.card=μ.card ∧
      (ν=μ ∨ List.Lex (· < ·) μ.rowLens ν.rowLens) ∧ hPartition ν=x} := rfl
example (μ : YoungDiagram) : psi3 (hPartition μ) ∈ Hge μ := psi3_mem_Hge μ
example (μ : YoungDiagram) : hBasis.repr (psi3 (hPartition μ)) μ=(-1 : ℤ)^(b μ.transpose) :=
  psi3_diagonal μ
example (μ ν : YoungDiagram)
    (hout : ν.card≠μ.card ∨ ¬ (ν=μ ∨ List.Lex (· < ·) μ.rowLens ν.rowLens)) :
    hBasis.repr (psi3 (hPartition μ)) ν=0 := psi3_coordinate_zero μ ν hout
example (μ : YoungDiagram) :
    psi3 (hPartition μ)-(-1 : ℤ)^(b μ.transpose) • hPartition μ ∈
      Submodule.span ℤ {x | ∃ ν : YoungDiagram, ν.card=μ.card ∧
        List.Lex (· < ·) μ.rowLens ν.rowLens ∧ hPartition ν=x} := psi3_triangular_remainder μ
example (μ : YoungDiagram) : ∃ a : YoungDiagram →₀ ℤ,
    psi3 (hPartition μ)=(-1 : ℤ)^(b μ.transpose) • hPartition μ + a.sum (fun ν z => z • hPartition ν) ∧
    (∀ ν, a ν≠0 → ν.card=μ.card ∧ List.Lex (· < ·) μ.rowLens ν.rowLens) := psi3_expansion μ
example (d : ℕ) (μ ν : DegreeShapes.DegreeShape d) :
    hBasis.repr (psi3 (hPartition μ.val)) μ.val=(-1 : ℤ)^(b μ.val.transpose) ∧
    (List.Lex (· < ·) ν.val.rowLens μ.val.rowLens →
      hBasis.repr (psi3 (hPartition μ.val)) ν.val=0) := degree_matrix_consumer d μ ν

end OddMath.Frontier.EKTriangularAudit

#check Hge
#check b
#check psi3_mem_Hge
#check psi3_diagonal
#check psi3_coordinate_zero
#check psi3_triangular_remainder
#check psi3_expansion
#check degree_matrix_consumer
#check word_upper
#check word_leading
#check reversal_sign
#check b_transpose

-- Complete enumeration by defining module, including every SAFE generated helper.
-- Unsafe compiler stages are individually listed, never silently excluded by name.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKTriangular,
        `OddMath.Frontier.EKTriangularControls,
        `OddMath.Frontier.EKTriangularAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``Hge, ``b, ``psi3_mem_Hge, ``psi3_diagonal,
      ``psi3_coordinate_zero, ``psi3_triangular_remainder, ``psi3_expansion,
      ``degree_matrix_consumer, ``word_upper, ``word_leading, ``pair_leading,
      ``normal_context_lt, ``reversal_sign, ``b_transpose,
      ``EKTriangularControls.empty_word, ``EKTriangularControls.repeated_parts,
      ``EKTriangularControls.first_noncommuting, ``EKTriangularControls.repeated_even,
      ``EKTriangularControls.mixed_degree_four, ``EKTriangularControls.wrong_diagonal_rejected,
      ``EKTriangularControls.wrong_reversal_rejected,
      ``EKTriangularControls.source_diagonal_sign_controls,
      ``EKTriangularControls.wrong_degree_coordinate,
      ``EKTriangularControls.printed_224_still_rejected,
      ``EKTriangularControls.general_consumer] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler && info.isUnsafe then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' unsafe=true depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' unsafe=false depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"

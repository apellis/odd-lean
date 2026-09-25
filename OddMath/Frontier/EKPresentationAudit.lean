import OddMath.Frontier.EKPresentationControls

open scoped BigOperators
open OddMath.Frontier EKRadicalQuotient EKPresentation

-- Definitional checks exclude a kernel/radical-defined presentation surrogate.
example : Presented = (CompleteElementary.A ⧸ relIdeal) := rfl
example : relIdeal = (TwoSidedIdeal.span {r : CompleteElementary.A | Relator r}).asIdeal := rfl
example : CompleteElementary.h 0 = 1 := rfl
example (n : ℕ) : CompleteElementary.h (n+1) = FreeAlgebra.ι ℤ n := rfl
example (a b : ℕ) (hab : Even (a+b)) :
    Relator (CompleteElementary.h a*CompleteElementary.h b -
      CompleteElementary.h b*CompleteElementary.h a) := Relator.even a b hab
example (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    Relator (CompleteElementary.h a*CompleteElementary.h b +
      (-1 : ℤ)^a • (CompleteElementary.h b*CompleteElementary.h a) -
      ((-1 : ℤ)^a • (CompleteElementary.h (a+1)*CompleteElementary.h (b-1)) +
        CompleteElementary.h (b-1)*CompleteElementary.h (a+1))) := Relator.odd a b hb hab
example (x : CompleteElementary.A) : toQ (mk x) = pi x := toQ_mk x
example : Function.Bijective toQ := toQ_bijective
example (n : ℕ) : presentationEquiv (h n) = EKElementaryQuotient.h n := presentationEquiv_h n
example (n : ℕ) : psi1 (EKElementaryQuotient.h n) = EKElementaryQuotient.e n := psi1_h n
example (z : ℤ) (x y : Q) : psi1 (z • (x*y)) = z • (psi1 x * psi1 y) := by
  rw [map_zsmul, map_mul]
example (x : Q) : psi1.symm (psi1 x) = x ∧ psi1 (psi1.symm x) = x :=
  ⟨psi1.symm_apply_apply x, psi1.apply_symm_apply x⟩
example (x : CompleteElementary.A) :
    psi1.symm (pi x) = pi (CompleteChangeOfGenerators.elementaryToComplete x) := psi1_symm_pi x
example (w : List ℕ) :
    word w ∈ Submodule.span ℤ (Set.range
      (fun μ : DegreeShapes.DegreeShape w.sum => word μ.val.rowLens)) := word_mem_degree_span w
example (w : List ℕ) :
    psi1 ((w.map EKElementaryQuotient.h).prod) = (w.map EKElementaryQuotient.e).prod := psi1_word w
example : psi1 (psi1 (EKElementaryQuotient.h 2)) ≠ EKElementaryQuotient.h 2 :=
  EKPresentationControls.psi1_not_involutive

#check Relator
#check Presented
#check pair_mem
#check word_mem_of_sorted
#check partition_span
#check toQ_bijective
#check presentationEquiv
#check psi1
#check psi1_h
#check psi1_pi
#check psi1_symm_pi
#check psi1_word
#check psi1_inverse_word
#print axioms toQ_bijective
#print axioms presentationEquiv
#print axioms psi1
#print axioms psi1_symm_pi
#print axioms EKPresentationControls.psi1_not_involutive

-- Audit all owned constants, including SAFE compiler-named generated helpers.
-- Only name-matched AND unsafe compiler artifacts are exempted and logged.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKPresentation,
        `OddMath.Frontier.EKPresentationControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``Relator, ``relSet, ``relTwoSided, ``relIdeal, ``Presented,
      ``complete_even, ``complete_odd, ``pair_mem, ``word_mem_of_sorted,
      ``word_mem_degree_span, ``partition_span, ``exists_expansion,
      ``toColor_injective, ``toColor_surjective, ``toQ_bijective,
      ``presentationEquiv, ``presentationEquiv_h, ``psi1, ``psi1_h,
      ``psi1_pi, ``psi1_symm_pi, ``psi1_symm_h, ``psi1_word, ``psi1_inverse_word,
      ``EKPresentationControls.degree_zero, ``EKPresentationControls.degree_one,
      ``EKPresentationControls.degree_two, ``EKPresentationControls.degree_three_ordered,
      ``EKPresentationControls.degree_three, ``EKPresentationControls.noncommuting_control,
      ``EKPresentationControls.prescribed_map_not_involutive,
      ``EKPresentationControls.psi1_not_involutive,
      ``EKPresentationControls.psi1_inverse_degree_two,
      ``EKPresentationControls.inverse_not_same,
      ``EKPresentationControls.arbitrary_word_consumer,
      ``EKPresentationControls.presented_boundary] do
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

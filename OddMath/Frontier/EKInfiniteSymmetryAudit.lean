import OddMath.Frontier.EKInfiniteSymmetryControls

noncomputable section
open OddMath.Frontier EKRadicalQuotient EKElementaryQuotient EKInfiniteSymmetry
open EKPresentation (psi1)
open EKAutomorphisms (psi2)
open EKAntipode (S)
namespace OddMath.Frontier.EKInfiniteSymmetryAudit

-- The carrier, coefficient ring, antipode and target multiplication are literal.
example : Q = (CompleteElementary.A ⧸ EKRadicalQuotient.radical) := rfl
example (x : Q) : S x = psi1 (psi2 (EKAutomorphisms.psi3 x)) := rfl
example (a b : Q ≃+* Q) (x : Q) : (a*b) x = a (b x) := rfl
example (k : ℕ) : (psi1^[k]) (h 2) = h 2-(k : ℤ) • (h 1*h 1) :=
  psi1_iterate_h_two k
example : orderOf psi1 = 0 := psi1_infinite_order
example (k : ℕ) : (S^[2*k]) (h 2) = h 2-((2*k : ℕ) : ℤ) • (h 1*h 1) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using S_even_iterate_h_two k
example (k : ℕ) (hk : 0 < k) : (S^[k]) ≠ id := S_no_positive_iterate k hk
example : Function.Injective (fun k : ℕ => (S^[2*k]) (h 2)) := S_even_orbit_injective
example : Function.Injective rho := rho_injective
example : rho (.r 1) = psi1 ∧ rho (.sr 0) = psi2 := ⟨rho_r_one, rho_sr_zero⟩
example : rho.range = Subgroup.closure {psi1, psi2} := range_eq_generated
example : DihedralGroup 0 ≃* Subgroup.closure {psi1, psi2} := dihedralEquiv
example : (dihedralEquiv (.r 1)).val = psi1 ∧ (dihedralEquiv (.sr 0)).val = psi2 := by
  simp
example (f : generated) : ∃! p : Bool × ℤ,
    f.val = (if p.1 then psi2*psi1^p.2 else psi1^p.2) := unique_normal_form f

end OddMath.Frontier.EKInfiniteSymmetryAudit

#check psi1_iterate_h_two
#check psi1_infinite_order
#check S_even_iterate_h_two
#check S_no_positive_iterate
#check S_even_orbit_injective
#check rho
#check rho_injective
#check range_eq_generated
#check dihedralEquiv
#check unique_normal_form
#check normal_form_action
#check EKInfiniteSymmetryControls.all_element_consumer
#check EKInfiniteSymmetryControls.orbit_consumer

-- Complete safe-owned transitive audit, including private/generated declarations.
-- Only genuinely unsafe compiler artifacts are separately classified.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKInfiniteSymmetry,
        `OddMath.Frontier.EKInfiniteSymmetryControls,
        `OddMath.Frontier.EKInfiniteSymmetryAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``square_smul_injective, ``square_ne_zero, ``h_one_ne_zero,
      ``h_one_ne_neg, ``translation_injective, ``psi1_iterate_h_two,
      ``psi1_infinite_order, ``S_even_iterate_h_two, ``S_even_orbit_injective,
      ``S_no_positive_iterate, ``rotation_values, ``rotation_cross,
      ``rho, ``rho_r_one, ``rho_sr_zero, ``reflection_h_one, ``reflection_h_two,
      ``rho_injective, ``generated, ``range_eq_generated, ``dihedralEquiv,
      ``unique_normal_form, ``normal_form_action,
      ``EKInfiniteSymmetryControls.degree_zero,
      ``EKInfiniteSymmetryControls.degree_one,
      ``EKInfiniteSymmetryControls.degree_two,
      ``EKInfiniteSymmetryControls.second_step,
      ``EKInfiniteSymmetryControls.multiplication_controls,
      ``EKInfiniteSymmetryControls.all_element_consumer,
      ``EKInfiniteSymmetryControls.orbit_consumer] do
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

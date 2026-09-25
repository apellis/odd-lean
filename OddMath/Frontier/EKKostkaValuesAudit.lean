import OddMath.Frontier.EKKostkaValues
import OddMath.Frontier.EKKostkaValuesControls

/-! Axiom audit (EK1107.5610v2 Thm 3.7 (3.9)).

1. Literal `#print axioms` for every named owned declaration.
2. An exhaustive sweep over EVERY constant whose defining module is
   `OddMath.Frontier.EKKostkaValues` or `OddMath.Frontier.EKKostkaValuesControls`
   (including private, auxiliary, equation and instance declarations): the
   build FAILS unless each depends only on propext, Classical.choice, Quot.sound.
3. Type-level restatement checks of the headline theorems. -/

open OddMath.Frontier.EKKostkaValues

#print axioms OddMath.Frontier.EKKostkaValues.tilde
#print axioms OddMath.Frontier.EKKostkaValues.tilde_add
#print axioms OddMath.Frontier.EKKostkaValues.tilde_mul_self
#print axioms OddMath.Frontier.EKKostkaValues.conv
#print axioms OddMath.Frontier.EKKostkaValues.conv_single_single
#print axioms OddMath.Frontier.EKKostkaValues.mul_apply_conv
#print axioms OddMath.Frontier.EKKostkaValues.sum_exponents
#print axioms OddMath.Frontier.EKKostkaValues.tilde_expSingle
#print axioms OddMath.Frontier.EKKostkaValues.sorted_word_prod
#print axioms OddMath.Frontier.EKKostkaValues.exponents_count
#print axioms OddMath.Frontier.EKKostkaValues.monotone_unique
#print axioms OddMath.Frontier.EKKostkaValues.monotone_exists
#print axioms OddMath.Frontier.EKKostkaValues.completePoly_apply
#print axioms OddMath.Frontier.EKKostkaValues.prodH
#print axioms OddMath.Frontier.EKKostkaValues.pairing_nil
#print axioms OddMath.Frontier.EKKostkaValues.pairing_one_row
#print axioms OddMath.Frontier.EKKostkaValues.crossingCount_eq_crossCols
#print axioms OddMath.Frontier.EKKostkaValues.prodH_apply
#print axioms OddMath.Frontier.EKKostkaValues.H_eq_prodH
#print axioms OddMath.Frontier.EKKostkaValues.Mh_eq_pairing
#print axioms OddMath.Frontier.EKKostkaValues.sp_coeff
#print axioms OddMath.Frontier.EKKostkaValues.Mh_eq_sum_kostka
#print axioms OddMath.Frontier.EKKostkaValues.directNorth_eq_sum_row
#print axioms OddMath.Frontier.EKKostkaValues.cells_box
#print axioms OddMath.Frontier.EKKostkaValues.directNorth_eq_choose
#print axioms OddMath.Frontier.EKKostkaValues.directNorth_eq_rows
#print axioms OddMath.Frontier.EKKostkaValues.sign_eq_even_rows
#print axioms OddMath.Frontier.EKKostkaValues.Mh_eq_sum_kostka_printed
#print axioms OddMath.Frontier.EKKostkaValues.Mh_eq_sum_kostka_choose
#print axioms OddMath.Frontier.EKKostkaValues.matrix_sum_eq_sum_kostka
#print axioms OddMath.Frontier.EKKostkaValues.kostka
#print axioms OddMath.Frontier.EKKostkaValues.Mh_eq_matrix

#print axioms OddMath.Frontier.EKKostkaValuesControls.dg
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_22
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_1111
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_111
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_2
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_11
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_211
#print axioms OddMath.Frontier.EKKostkaValuesControls.directNorth_321
#print axioms OddMath.Frontier.EKKostkaValuesControls.mh_degree_two
#print axioms OddMath.Frontier.EKKostkaValuesControls.kostka_diag_degree_two

open Lean Elab Command in
/-- Exhaustive per-module axiom sweep; throws on any non-standard axiom. -/
elab "#audit_module_axioms " mod:ident : command => do
  let env ← getEnv
  let modName := mod.getId
  let some idx := env.getModuleIdx? modName
    | throwError "module {modName} is not imported"
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut bad : Array (Name × Array Name) := #[]
  for n in names do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => std.contains a) do
      bad := bad.push (n, axs)
  logInfo m!"{modName}: {names.size} constants audited; non-standard: {bad.size}"
  unless bad.isEmpty do
    throwError m!"non-standard axioms: {bad.toList}"

#audit_module_axioms OddMath.Frontier.EKKostkaValues
#audit_module_axioms OddMath.Frontier.EKKostkaValuesControls

/-! Headline statements, restated at the type level (definitional check). -/
open OddMath.Frontier in
example (d : ℕ) (μ ρ : DegreeShapes.DegreeShape d) :
    EKDualBases.Mh d μ ρ = @Finset.sum _ _ _ (@Finset.univ _ (DegreeShapes.degreeFintype d))
      (fun lam => (-1 : ℤ) ^ (∑ i ∈ (Finset.range (lam.val.colLen 0)).filter (fun i => i % 2 = 1),
        lam.val.rowLen i) * TableauDominance.signedKostka lam.val μ.val *
          TableauDominance.signedKostka lam.val ρ.val) :=
  Mh_eq_sum_kostka_printed d μ ρ

open OddMath.Frontier in
example (d : ℕ) (μ ρ : DegreeShapes.DegreeShape d) :
    EKDualBases.Mh d μ ρ = @Finset.sum _ _ _ (@Finset.univ _ (DegreeShapes.degreeFintype d))
      (fun lam => (-1 : ℤ) ^ (∑ j ∈ Finset.range (lam.val.rowLen 0), (lam.val.colLen j).choose 2) *
        TableauDominance.signedKostka lam.val μ.val * TableauDominance.signedKostka lam.val ρ.val) :=
  Mh_eq_sum_kostka_choose d μ ρ

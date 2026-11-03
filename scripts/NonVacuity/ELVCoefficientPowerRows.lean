import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerRows
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega

private def deltaA (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private theorem deltaA_mem (i : Bool) :
    deltaA i ∈ SKM.SYM.elvCoefficientParity D cutoff 1 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_delta_mem_odd D (k := ℚ) ⟨i, rfl⟩)
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, deltaA] using h

private theorem deltaClass_ne_zero (i : Bool) :
    coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by norm_num [cutoff])
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩⟩)
    (a₂ := 0) (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨i, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)


private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private abbrev M := coefficientPowerVacuum D Sc cutoff L
private def dot (i : Bool) : Module.End ℚ (mateTargetSpace D Sc cutoff i M ⟨[]⟩) :=
  actualInductionDot D Sc cutoff i M ((append D Sc cutoff i).obj ⟨[]⟩)
private def deltaClass (j : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨j, rfl⟩)
private def outputCoefficient (i j : Bool) :
    Module.End ℚ (mateTargetSpace D Sc cutoff i M ⟨[]⟩) :=
  SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).map
      (X := ⟨[]⟩) (Y := ⟨[]⟩) (coefficientEndomorphism D Sc cutoff [] (deltaA j)))

/-- Extraction is an identity on every literal power-quotient vector at
its top slot, including both occupied exterior directions. -/
example (i : Bool) (z : AQ) :
    functional D Sc cutoff L i (by norm_num [cutoff]) ((dot i ^ 3) (unit D Sc cutoff L i z)) = z := by
  exact functional_dot_window D Sc cutoff L i (by norm_num [cutoff]) 3 (by norm_num [cutoff]) z

/-- The lower window is tested without any nonzero or homogeneity premise. -/
example (i : Bool) (z : AQ) : functional D Sc cutoff L i (by norm_num [cutoff])
    ((dot i ^ 2) (unit D Sc cutoff L i z)) = 0 := by
  exact functional_dot_window D Sc cutoff L i (by norm_num [cutoff]) 2 (by norm_num [cutoff]) z

/-- Each odd coefficient remains occupied after the prescribed top dotted
unit; its nonzero extraction witnesses that the mate target is occupied. -/
example (i j : Bool) : (dot i ^ 3) (unit D Sc cutoff L i (deltaClass j)) ≠ 0 := by
  intro hz
  have h := functional_dot_window D Sc cutoff L i (by norm_num [cutoff]) 3 (by norm_num [cutoff]) (deltaClass j)
  change functional D Sc cutoff L i (by norm_num [cutoff])
    ((dot i ^ 3) (unit D Sc cutoff L i (deltaClass j))) = deltaClass j at h
  rw [hz, map_zero] at h
  exact deltaClass_ne_zero j h.symm

/-- An odd coefficient passing through the odd top row contributes the
minus sign, with its original left multiplication order. -/
example (i j : Bool) (z : mateTargetSpace D Sc cutoff i M ⟨[]⟩) :
    functional D Sc cutoff L i (by norm_num [cutoff]) (outputCoefficient i j z) =
      -(deltaClass j * functional D Sc cutoff L i (by norm_num [cutoff]) z) := by
  have h := functional_coefficient D Sc cutoff L i (by norm_num [cutoff]) (deltaA_mem j) z
  change functional D Sc cutoff L i (by norm_num [cutoff]) (outputCoefficient i j z) =
    koszulSign ((cutoff i - 1) • D.parity i) 1 •
      (deltaClass j * functional D Sc cutoff L i (by norm_num [cutoff]) z) at h
  have hp : (cutoff i - 1) • D.parity i = (1 : ZMod 2) := by
    change (3 : ℕ) • (1 : ZMod 2) = 1
    decide
  simpa only [hp, koszulSign_one_one, neg_one_zsmul] using h

/-- The signed coefficient rule is nonzero on the top dotted ordinary
unit. It would fail if the inverse row were incorrectly treated as even. -/
example (i j : Bool) :
    functional D Sc cutoff L i (by norm_num [cutoff])
      (outputCoefficient i j ((dot i ^ 3) (unit D Sc cutoff L i 1))) = -deltaClass j := by
  have h := functional_coefficient D Sc cutoff L i (by norm_num [cutoff]) (deltaA_mem j)
    ((dot i ^ 3) (unit D Sc cutoff L i 1))
  change functional D Sc cutoff L i (by norm_num [cutoff])
    (outputCoefficient i j ((dot i ^ 3) (unit D Sc cutoff L i 1))) =
      koszulSign ((cutoff i - 1) • D.parity i) 1 •
        (deltaClass j * functional D Sc cutoff L i (by norm_num [cutoff])
          ((dot i ^ 3) (unit D Sc cutoff L i 1))) at h
  have hw := functional_dot_window D Sc cutoff L i (by norm_num [cutoff]) 3 (by norm_num [cutoff]) (1 : AQ)
  change functional D Sc cutoff L i (by norm_num [cutoff]) ((dot i ^ 3) (unit D Sc cutoff L i 1)) = 1 at hw
  have hp : (cutoff i - 1) • D.parity i = (1 : ZMod 2) := by
    change (3 : ℕ) • (1 : ZMod 2) = 1
    decide
  simpa only [hp, koszulSign_one_one, neg_one_zsmul, hw, mul_one] using h


private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { D with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => D.even_of_odd i j rfl }
private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

/-- The same literal power-vacuum extraction window also applies to a
mixed datum, checking an even and an odd moving colour. -/
example (i : Bool) (z : CoefficientPowerQuotient (k := ℚ) mixedDatum cutoff L) :
    functional mixedDatum mixedScalars cutoff L i (by norm_num [cutoff])
      ((actualInductionDot mixedDatum mixedScalars cutoff i
        (coefficientPowerVacuum mixedDatum mixedScalars cutoff L)
          ((append mixedDatum mixedScalars cutoff i).obj ⟨[]⟩) ^ 3)
        (unit mixedDatum mixedScalars cutoff L i z)) = z :=
  functional_dot_window mixedDatum mixedScalars cutoff L i (by norm_num [cutoff])
    3 (by norm_num [cutoff]) z

end NonVacuity.ELVCoefficientPowerRows

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMoments
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerMoments
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 2
private def L (_ : Bool × ℕ) : ℕ := 2
private theorem positive (i : Bool) : 0 < cutoff i := by change 0 < 2; decide
private theorem first_below (i : Bool) : 1 < cutoff i := by change 1 < 2; decide
private theorem powers_high (a : Bool × ℕ) :
    2 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 2 ≤ 2 * SKM.SYM.elementaryWeight D a
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
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 2 (by decide)
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩⟩)
    (a₂ := 0) (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨i, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)



private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)

/-- The raw top moment has the odd inverse row's coefficient sign. -/
private theorem raw_delta_one (i j : Bool) :
    rawMoment D Sc cutoff L i (positive i) (deltaA j) 1 = -deltaClass j := by
  have h := rawMoment_window D Sc cutoff L i (positive i) 1
    (first_below i) (deltaA_mem j)
  have hp : (cutoff i - 1) • D.parity i = (1 : ZMod 2) := by
    change 1 • (1 : ZMod 2) = 1
    exact one_nsmul _
  change rawMoment D Sc cutoff L i (positive i) (deltaA j) 1 =
    koszulSign ((cutoff i - 1) • D.parity i) 1 •
      (deltaClass j * (inductionUnitDotSign (k := ℚ) (D.parity i) 1 •
        (if 1 + 1 = cutoff i then 1 else 0))) at h
  have ht : 1 + 1 = cutoff i := rfl
  simpa only [hp, koszulSign_one_one, ht, ↓reduceIte, inductionUnitDotSign,
    Nat.choose_eq_zero_of_lt (by decide : 1 < 2), zero_nsmul, sign_zero,
    one_smul, mul_one, neg_one_zsmul] using h

/-- The first unknown raw moment is determined by the literal old
cyclotomic relation, including its odd coefficient. -/
private theorem raw_one_two (i : Bool) :
    rawMoment D Sc cutoff L i (positive i) 1 2 = deltaClass i := by
  have h := rawMoment_leading D Sc cutoff L i (positive i) 1 0
  change rawMoment D Sc cutoff L i (positive i) 1 2 =
    -(∑ j : Fin 2, rawMoment D Sc cutoff L i (positive i)
      (1 * singleCoefficient D cutoff i j.castSucc) (j.val + 0)) at h
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.add_zero, one_mul] at h
  have hzero := rawMoment_window D Sc cutoff L i (positive i) 0
    (positive i) (singleCoefficient_mem D cutoff i (0 : Fin 2).castSucc)
  have ht : ¬ 0 + 1 = cutoff i := by change ¬ 1 = 2; decide
  rw [ite_eq_right ht, smul_zero, mul_zero, smul_zero] at hzero
  have hcoeff : singleCoefficient (k := ℚ) D cutoff i (1 : Fin 2).castSucc = deltaA i := by
    have hp : D.parity i = 1 := rfl
    unfold singleCoefficient
    rw [dite_eq_left hp]
    change SKM.SYM.elvCoefficientQuotient D cutoff
      (((-1 : ℚ) ^ (2 * (1 + 1))) • SKM.SYM.elvCoefficient D ℚ ⟨i, hp⟩ (2 - 1)) = deltaA i
    norm_num [SKM.SYM.elvCoefficient, SKM.SYM.elvChi, deltaA]
  rw [hzero, hcoeff, raw_delta_one, zero_add, neg_neg] at h
  exact h

/-- The actual signed higher moment recovers a nonzero odd coefficient
with its minus sign in literal A/T. -/
private theorem signed_one_two (i : Bool) :
    signedMoment D Sc cutoff L i (positive i) 2 = -deltaClass i := by
  have h := signedMoment_rawMoment D Sc cutoff L i (positive i) 2
  rw [raw_one_two] at h
  change signedMoment D Sc cutoff L i (positive i) 2 = (-1 : ℚ) • deltaClass i at h
  exact h.trans (neg_one_smul ℚ (deltaClass i))

example (i : Bool) : signedMoment D Sc cutoff L i (positive i) 2 = -deltaClass i :=
  signed_one_two i

example (i : Bool) : signedMoment D Sc cutoff L i (positive i) 2 ≠ 0 := by
  rw [signed_one_two, neg_ne_zero]
  exact deltaClass_ne_zero i

/-- The complete higher signed recurrence is instantiated in the same
occupied literal power vacuum, without an extra relation premise. -/
example (i : Bool) (m : ℕ) :
    (∑ j : Fin 3,
      koszulSign ((cutoff i - 1) • D.parity i)
        ((cutoff i : ZMod 2) * D.parity i - j.val • D.parity i) •
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := ℚ) D cutoff) L).ringCon.mkₐ ℚ
        (singleCoefficient D cutoff i j) *
          (inductionUnitDotSign (k := ℚ) (D.parity i) (j.val + m) •
            signedMoment D Sc cutoff L i (positive i) (j.val + m)))) = 0 :=
  signedMoment_recurrence D Sc cutoff L i (positive i) m

end NonVacuity.ELVCoefficientPowerMoments

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMoments
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRemainders
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerRemainders
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 2
private def L (_ : Bool × ℕ) : ℕ := 2
private theorem positive (i : Bool) : 0 < cutoff i := by change 0 < 2; decide
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
private abbrev q :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := ℚ) D cutoff) L).ringCon.mkₐ ℚ
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)

/-- The actual complete ordinary remainder series is the formal inverse
of the reversed literal monic relation over A/T. -/
example (i : Bool) : remainderSeries D Sc cutoff L i (positive i) =
    PowerSeries.invOfUnit (remainderPolynomial D cutoff L i) 1 :=
  remainderSeries_eq_invOfUnit D Sc cutoff L i rfl (positive i)

example (i : Bool) :
    remainderSeries D Sc cutoff L i (positive i) * remainderPolynomial D cutoff L i = 1 := by
  rw [remainderSeries_eq_invOfUnit D Sc cutoff L i rfl (positive i)]
  exact PowerSeries.invOfUnit_mul _ _ (remainderPolynomial_constantCoeff D Sc cutoff L i rfl (positive i))

private theorem remainder_one (i : Bool) :
    remainder D Sc cutoff L i (positive i) 1 = -deltaClass i := by
  have h := remainder_recurrence D Sc cutoff L i rfl (positive i) 1 (by decide)
  have htop : singleCoefficient (k := ℚ) D cutoff i (2 : Fin 3) = 1 :=
    singleCoefficient_top D cutoff i
  have hcoeff : singleCoefficient (k := ℚ) D cutoff i (1 : Fin 3) = deltaA i := by
    have hp : D.parity i = 1 := rfl
    unfold singleCoefficient
    rw [dite_eq_left hp]
    change SKM.SYM.elvCoefficientQuotient D cutoff
      (((-1 : ℚ) ^ (2 * (1 + 1))) • SKM.SYM.elvCoefficient D ℚ ⟨i, hp⟩ (2 - 1)) = deltaA i
    norm_num [SKM.SYM.elvCoefficient, SKM.SYM.elvChi, deltaA]
  have hz : q (singleCoefficient D cutoff i (1 : Fin 3)) *
      remainder D Sc cutoff L i (positive i) 0 +
      remainder D Sc cutoff L i (positive i) 1 = 0 := by
    change (∑ j : Fin 3, q (singleCoefficient D cutoff i j) *
      (if 2 - j.val ≤ 1 then remainder D Sc cutoff L i (positive i) (1 - (2 - j.val))
       else 0)) = 0 at h
    rw [Fin.sum_univ_three] at h
    norm_num [htop] at h
    exact h
  rw [remainder_zero D Sc cutoff L i rfl (positive i), mul_one, hcoeff] at hz
  change deltaClass i + remainder D Sc cutoff L i (positive i) 1 = 0 at hz
  exact eq_neg_of_add_eq_zero_right hz

/-- The first ordinary remainder and its signed higher moment are both
occupied; the sign agrees with the actual odd monic relation. -/
example (i : Bool) : remainder D Sc cutoff L i (positive i) 1 ≠ 0 := by
  rw [remainder_one, neg_ne_zero]
  exact deltaClass_ne_zero i

example (i : Bool) : signedMoment D Sc cutoff L i (positive i) 2 = -deltaClass i := by
  have h := signedMoment_remainder D Sc cutoff L i rfl (positive i) 1
  change signedMoment D Sc cutoff L i (positive i) 2 = _ at h
  simpa only [Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero,
    Supercategory.sign_zero, one_smul, remainder_one] using h

/-- Every higher signed/ordinary normalization, including the triangular
coefficient-parity correction, is tested on this literal power vacuum. -/
example (i : Bool) (l : ℕ) :
    signedMoment D Sc cutoff L i (positive i) (1 + l) =
      sign ℚ ((l.choose 2 : ℕ) : ZMod 2) • remainder D Sc cutoff L i (positive i) l :=
  signedMoment_remainder D Sc cutoff L i rfl (positive i) l

/-- The even-cutoff top exterior relation is retained. The tail is not
replaced by an independent polynomial/exterior tensor algebra. -/
example (i : Bool) : coefficientPowerQuotientMap (k := ℚ) D cutoff L
    (SKM.SYM.delta D ℚ ⟨i, rfl⟩ * SKM.SYM.e D ℚ i 0) = 0 := by
  have h := odd_coefficient_tail (k := ℚ) D cutoff L i rfl 3 (by change 2 < 3; decide)
  exact h

end NonVacuity.ELVCoefficientPowerRemainders

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRemainders
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

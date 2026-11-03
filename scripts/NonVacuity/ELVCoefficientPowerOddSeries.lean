import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerOddSeries
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerOddSeries
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private def elementaryClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.e D ℚ i 0)

private theorem window_ne_zero {d : ℕ} (hd : d < 4) (a : SKM.SYM D ℚ)
    (ha : a ∈ SKM.SYM.CoefficientAtMost D ℚ d) (h0 : a ≠ 0) :
    coefficientPowerQuotientMap D cutoff L a ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L d 4 hd large powers_high
  have he := hi (a₁ := ⟨a, ha⟩) (a₂ := 0)
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  exact h0 (congrArg Subtype.val he)

private theorem delta_ne_zero (i : Bool) : deltaClass i ≠ 0 := by
  apply window_ne_zero (by decide : 1 < 4) _ (SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩)
  rw [← SKM.SYM.coefficientBasis_delta]
  exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _

private theorem elementary_mem (i : Bool) :
    SKM.SYM.e D ℚ i 0 ∈ SKM.SYM.CoefficientAtMost D ℚ 2 := by
  have h := SKM.SYM.e_mem_coefficientAtMost D ℚ i 0
  exact h

private theorem elementary_ne_zero (i : Bool) : elementaryClass i ≠ 0 := by
  apply window_ne_zero (by decide : 2 < 4) _ (elementary_mem i)
  rw [← SKM.SYM.coefficientBasis_elementary]
  exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _

private theorem delta_elementary_ne_zero (i : Bool) : deltaClass i * elementaryClass i ≠ 0 := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D ℚ i 0) ≠ 0
  rw [← map_mul]
  have hm : SKM.SYM.delta D ℚ ⟨i, rfl⟩ * SKM.SYM.e D ℚ i 0 ∈
      SKM.SYM.CoefficientAtMost D ℚ 3 :=
    SKM.SYM.coefficientAtMost_mul D ℚ (m := 1) (n := 2)
      (x := SKM.SYM.delta D ℚ ⟨i, rfl⟩) (y := SKM.SYM.e D ℚ i 0)
      (SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩) (elementary_mem i)
  apply window_ne_zero (by decide : 3 < 4) _ hm
  have he : SKM.SYM.coefficientBasis D ℚ (Finsupp.single (i, 0) 1, {⟨i, rfl⟩}) =
      SKM.SYM.delta D ℚ ⟨i, rfl⟩ * SKM.SYM.e D ℚ i 0 := by
    rw [SKM.SYM.coefficientBasis_eq_mul, ← MvPolynomial.X,
      SKM.SYM.polynomialInclude_X, SKM.SYM.oddExteriorBasis_singleton]
    simpa only [SKM.SYM.exteriorInclude_ι, SKM.SYM.oddLinear_single, one_smul] using
      (SKM.SYM.e_delta_commute D ℚ i 0 ⟨i, rfl⟩).eq
  rw [← he]
  exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _

private theorem inverse_coeff_one {R : Type*} [Ring R] (f : PowerSeries R) :
    PowerSeries.coeff 1 (PowerSeries.invOfUnit f 1) = -PowerSeries.coeff 1 f := by
  have hanti : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  rw [PowerSeries.coeff_invOfUnit]
  norm_num [hanti, PowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem complete_one (i : Bool) : completeCoefficient D cutoff L i 1 = elementaryClass i := by
  rw [completeCoefficient, inverse_coeff_one, PowerSeries.coeff_rescale]
  simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, polynomialToPower,
    AlgHom.comp_apply, elementaryClass]

/-- Both complete parity series hold on the actual power vacuum at two
different odd-colour cutoff parities, for every coefficient index. -/
example (i : Bool) (r : ℕ) :
    signedMoment D Sc cutoff L i (positive i) (cutoff i - 1 + 2 * r) =
      completeCoefficient D cutoff L i r :=
  signedMoment_even D Sc cutoff L i rfl (positive i) r

example (i : Bool) (r : ℕ) :
    signedMoment D Sc cutoff L i (positive i) (cutoff i - 1 + (2 * r + 1)) =
      (-1 : ℚ) ^ (cutoff i + 1) • (deltaClass i * completeCoefficient D cutoff L i r) :=
  signedMoment_odd D Sc cutoff L i rfl (positive i) r

private theorem first_four : signedMoment D Sc cutoff L false (positive false) 4 = -deltaClass false := by
  have h := signedMoment_first_odd D Sc cutoff L false rfl (positive false)
  change signedMoment D Sc cutoff L false (positive false) 4 = ((-1 : ℚ) ^ 5) • deltaClass false at h
  rw [show (-1 : ℚ) ^ 5 = -1 by norm_num] at h
  exact h.trans (neg_one_smul ℚ (deltaClass false))

private theorem first_five : signedMoment D Sc cutoff L true (positive true) 5 = deltaClass true := by
  have h := signedMoment_first_odd D Sc cutoff L true rfl (positive true)
  change signedMoment D Sc cutoff L true (positive true) 5 = ((-1 : ℚ) ^ 6) • deltaClass true at h
  rw [show (-1 : ℚ) ^ 6 = 1 by norm_num, one_smul] at h
  exact h

/-- The two distinct exterior classes remain occupied, with opposite
normalization signs at even and odd cutoffs. -/
example : signedMoment D Sc cutoff L false (positive false) 4 ≠ 0 := by
  rw [first_four, neg_ne_zero]
  exact delta_ne_zero false

example : signedMoment D Sc cutoff L true (positive true) 5 ≠ 0 := by
  rw [first_five]
  exact delta_ne_zero true

private theorem even_first (i : Bool) :
    signedMoment D Sc cutoff L i (positive i) (cutoff i + 1) = elementaryClass i := by
  have h := signedMoment_even D Sc cutoff L i rfl (positive i) 1
  rw [show cutoff i - 1 + 2 * 1 = cutoff i + 1 by have hp := positive i; omega, complete_one] at h
  exact h

/-- The first nonconstant even-series coefficient is not removed by the
power quotient; the closed formula tests an occupied elementary direction. -/
example (i : Bool) : signedMoment D Sc cutoff L i (positive i) (cutoff i + 1) ≠ 0 := by
  rw [even_first]
  exact elementary_ne_zero i

/-- The next odd-series coefficient has both a polynomial and exterior
factor, and survives. Its multiplication order is unchanged. -/
example (i : Bool) :
    signedMoment D Sc cutoff L i (positive i) (cutoff i + 2) =
      (-1 : ℚ) ^ (cutoff i + 1) • (deltaClass i * elementaryClass i) := by
  have h := signedMoment_odd D Sc cutoff L i rfl (positive i) 1
  rw [show cutoff i - 1 + (2 * 1 + 1) = cutoff i + 2 by have hp := positive i; omega, complete_one] at h
  exact h

example (i : Bool) : deltaClass i * completeCoefficient D cutoff L i 1 ≠ 0 := by
  rw [complete_one]
  exact delta_elementary_ne_zero i

end NonVacuity.ELVCoefficientPowerOddSeries

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerOddSeries
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

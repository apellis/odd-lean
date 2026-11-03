import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerGrading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace NonVacuity.ELVCoefficientPowerGrading
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
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
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide)
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩⟩)
    (a₂ := 0) (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨i, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)

/-- Both independent odd coefficients survive the actual power quotient
and retain their literal odd superspace part. -/
example (i : Bool) :
    coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ∈
      (coefficientPowerSpace (k := ℚ) D cutoff L).part 1 :=
  coefficientPowerQuotient_mem D cutoff L (deltaA_mem i)

example (i : Bool) :
    coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ≠ 0 :=
  deltaClass_ne_zero i

private abbrev star := SuperalgebraCat.star (SKM.SYM.elvCoefficientParity (k := ℚ) D cutoff)
private def oddArrow (i : Bool) : star ⟶ star := SuperalgebraCat.ofElem (deltaA i)

/-- The actual regular quotient module has occupied odd coefficient
operators, with the unchanged coefficient action. -/
example (i : Bool) :
    (coefficientPowerRegular D cutoff L).map (X := star) (Y := star) (oddArrow i) ∈
      parity (R := ℚ) (coefficientPowerSpace (k := ℚ) D cutoff L)
        (coefficientPowerSpace (k := ℚ) D cutoff L) 1 :=
  IsSuperfunctor.map_mem (F := (coefficientPowerRegular D cutoff L).toFunctor) (deltaA_mem i)

example (i : Bool) :
    (coefficientPowerRegular D cutoff L).map (X := star) (Y := star) (oddArrow i) ≠ 0 := by
  intro hz
  have h := congrArg (fun f : CoefficientPowerQuotient (k := ℚ) D cutoff L →ₗ[ℚ]
      CoefficientPowerQuotient (k := ℚ) D cutoff L => f 1) hz
  change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := ℚ) D cutoff) L).ringCon.mkₐ ℚ
    (deltaA i) * 1 = 0 at h
  rw [mul_one] at h
  exact deltaClass_ne_zero i h

/-- The actual power generator acts as zero on every regular-module
vector, including its odd exterior directions. -/
example (x : CoefficientPowerQuotient (k := ℚ) D cutoff L) :
    (coefficientPowerRegular D cutoff L).map
      (SuperalgebraCat.ofElem ((elementaryCoefficients (k := ℚ) D cutoff (false, 0)) ^ 4) :
        star ⟶ star) x = 0 :=
  coefficientPowerRegular_kills D cutoff L
    (TwoSidedIdeal.subset_span (Set.mem_range_self (false, 0))) x

end NonVacuity.ELVCoefficientPowerGrading

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientCategory,
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerGrading] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations: {owner}"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"

import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerQuotient
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.SKM OddMath.SKM.SYM
open scoped Classical
namespace NonVacuity.ELVCoefficientPowerQuotient
open OddMath.QuiverHecke.ELVOld

private abbrev D := QuiverHecke.CyclotomicAction.AsymmetricParameters.datum
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4

private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * elementaryWeight D a := by
  change 4 ≤ 4 * elementaryWeight D a
  have hw : 0 < elementaryWeight D a := by
    unfold elementaryWeight
    split_ifs <;> omega
  omega

private def exteriorIndex : CoefficientIndex D :=
  (0, {⟨false, rfl⟩, ⟨true, rfl⟩})

private theorem exterior_mem : coefficientBasis D ℚ exteriorIndex ∈ CoefficientAtMost D ℚ 2 := by
  apply Submodule.subset_span
  refine ⟨exteriorIndex, ?_, rfl⟩
  simp [coefficientWeight, exteriorIndex]

/-- The independent two-odd exterior monomial survives the LITERAL
quotient of the actual ELV coefficient algebra by its power ideal. -/
example : coefficientPowerQuotientMap (k := ℚ) D cutoff L (coefficientBasis D ℚ exteriorIndex) ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 2 4 (by decide)
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, exterior_mem⟩) (a₂ := 0)
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  exact (coefficientBasis D ℚ).ne_zero exteriorIndex (congrArg Subtype.val he)

/-- The quotient comparison carries the original coefficient class to
its namesake universal class, including its exterior product. -/
example : coefficientPowerQuotientEquiv (k := ℚ) D cutoff L
      (coefficientPowerQuotientMap (k := ℚ) D cutoff L (coefficientBasis D ℚ exteriorIndex)) =
    (elvCoefficientIdeal D ℚ cutoff ⊔ coefficientPowerIdeal D ℚ L).ringCon.mkₐ ℚ
      (coefficientBasis D ℚ exteriorIndex) := rfl

example (x : CoefficientPowerQuotient (k := ℚ) D cutoff L) :
    (coefficientPowerQuotientEquiv (k := ℚ) D cutoff L).symm
      (coefficientPowerQuotientEquiv (k := ℚ) D cutoff L x) = x :=
  (coefficientPowerQuotientEquiv (k := ℚ) D cutoff L).symm_apply_apply x

example : coefficientPowerQuotientMap (k := ℚ) D cutoff L (e D ℚ false 0 ^ 4) = 0 := by
  apply (coefficientPowerQuotientEquiv (k := ℚ) D cutoff L).injective
  have hz : (elvCoefficientIdeal D ℚ cutoff ⊔ coefficientPowerIdeal D ℚ L).ringCon.mkₐ ℚ
      (e D ℚ false 0 ^ 4) = 0 := by
    exact Quotient.sound ((le_sup_right : coefficientPowerIdeal D ℚ L ≤
      elvCoefficientIdeal D ℚ cutoff ⊔ coefficientPowerIdeal D ℚ L)
        (TwoSidedIdeal.subset_span ⟨(false, 0), rfl⟩))
  exact hz.trans (map_zero (coefficientPowerQuotientEquiv (k := ℚ) D cutoff L)).symm

/-- The exterior anticommutation law survives the actual power quotient,
with the same original order and sign. -/
example :
    coefficientPowerQuotientMap (k := ℚ) D cutoff L (delta D ℚ ⟨false, rfl⟩) *
        coefficientPowerQuotientMap (k := ℚ) D cutoff L (delta D ℚ ⟨true, rfl⟩) =
      -(coefficientPowerQuotientMap (k := ℚ) D cutoff L (delta D ℚ ⟨true, rfl⟩) *
        coefficientPowerQuotientMap (k := ℚ) D cutoff L (delta D ℚ ⟨false, rfl⟩)) := by
  rw [← map_mul, delta_anticommute, map_neg, map_mul]

end NonVacuity.ELVCoefficientPowerQuotient

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerQuotient | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"

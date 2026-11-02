import OddMath.SKM.ELVCoefficientPowers
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.SKM OddMath.SKM.SYM
open scoped Classical
namespace NonVacuity.ELVCoefficientPowers

private abbrev D := QuiverHecke.CyclotomicAction.AsymmetricParameters.datum
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4

private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * elementaryWeight D a := by
  change 4 ≤ 4 * elementaryWeight D a
  have hw : 0 < elementaryWeight D a := by
    unfold elementaryWeight
    split_ifs <;> omega
  omega

private theorem keys : elvPolynomialKeys D cutoff =
    {(false, 0), (false, 1), (true, 0), (true, 1)} := by
  ext ⟨i, r⟩
  rw [mem_elvPolynomialKeys]
  cases i <;> simp [elvElementaryRank, cutoff, D,
    QuiverHecke.CyclotomicAction.AsymmetricParameters.datum] <;> omega

/-- The exact upper bound includes both independent exterior generators. -/
private theorem weightBound : elvPowerWeightBound D cutoff L = 38 := by
  rw [elvPowerWeightBound, keys]
  norm_num [elementaryWeight, L, D,
    QuiverHecke.CyclotomicAction.AsymmetricParameters.datum]

example : coefficientIdeal D ℚ 39 ≤
    elvCoefficientIdeal D ℚ cutoff ⊔ coefficientPowerIdeal D ℚ L := by
  simpa only [weightBound] using coefficientIdeal_le_elv_sup_power D ℚ cutoff L

example : elvCoefficientIdeal D ℚ cutoff ⊔ coefficientPowerIdeal D ℚ L ≤
    coefficientIdeal D ℚ 4 :=
  elv_sup_power_le_coefficientIdeal D ℚ cutoff L 4 (fun _ => by rfl) powers_high

private def exteriorIndex : CoefficientIndex D :=
  (0, {⟨false, rfl⟩, ⟨true, rfl⟩})

private theorem exterior_mem : coefficientBasis D ℚ exteriorIndex ∈ CoefficientAtMost D ℚ 2 := by
  apply Submodule.subset_span
  refine ⟨exteriorIndex, ?_, rfl⟩
  simp [coefficientWeight, exteriorIndex]

/-- An independent two-odd exterior monomial survives the actual power
quotient. This is not a test in the scalar specialization. -/
example : (elvCoefficientIdeal D ℚ cutoff ⊔ coefficientPowerIdeal D ℚ L).ringCon.mk'
    (coefficientBasis D ℚ exteriorIndex) ≠ 0 := by
  intro hz
  have hi := elvPower_quotient_injective D ℚ cutoff L 2 4 (by decide)
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, exterior_mem⟩) (a₂ := 0) (by simpa using hz)
  exact (coefficientBasis D ℚ).ne_zero exteriorIndex (congrArg Subtype.val he)

private def mixedD : Datum Bool (Bool → ℤ) :=
  { D with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => D.even_of_odd i j rfl }

/-- Both moving parities use the same power ideal and retain the cutoff's
literal elementary ranks. -/
example : coefficientIdeal mixedD ℚ (elvPowerWeightBound mixedD cutoff L + 1) ≤
    elvCoefficientIdeal mixedD ℚ cutoff ⊔ coefficientPowerIdeal mixedD ℚ L :=
  coefficientIdeal_le_elv_sup_power mixedD ℚ cutoff L

/-- Zero cutoffs require no positive-rank hypothesis. -/
example : coefficientIdeal D ℚ (elvPowerWeightBound D (fun _ => 0) L + 1) ≤
    elvCoefficientIdeal D ℚ (fun _ => 0) ⊔ coefficientPowerIdeal D ℚ L :=
  coefficientIdeal_le_elv_sup_power D ℚ (fun _ => 0) L

end NonVacuity.ELVCoefficientPowers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.ELVCoefficientPowers
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"

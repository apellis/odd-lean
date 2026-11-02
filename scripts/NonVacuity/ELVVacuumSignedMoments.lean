import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSignedMoments
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.VacuumCoefficient
open CyclotomicAction.AsymmetricParameters
namespace NonVacuity.ELVVacuumSignedMoments

private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }
private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def cutoff (_ : Bool) : ℕ := 2
private def oddIndex : SKM.SYM.CoefficientIndex mixedDatum := (0, {⟨true, rfl⟩})
private def oddCoefficient : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) mixedDatum cutoff :=
  SKM.SYM.elvCoefficientQuotient mixedDatum cutoff
    (SKM.SYM.coefficientBasis mixedDatum ℚ oddIndex)
private theorem oddCoefficient_mem :
    oddCoefficient ∈ SKM.SYM.elvCoefficientParity mixedDatum cutoff 1 := by
  have h := SKM.SYM.elvModelQuotient_mem mixedDatum (cutoff := cutoff)
    (SKM.SYM.coefficientBasis_mem_parity mixedDatum ℚ oddIndex)
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, oddCoefficient, oddIndex, Finset.card_singleton, Nat.cast_one] using h

/-- Beyond the extraction window, the second odd signed dot contributes
its triangular sign on the literal exterior coefficient. -/
example : signedMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 2 =
    -(coefficientMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 2) := by
  have h := signedMoment_coefficientMoment mixedDatum mixedScalars cutoff true
    (by decide) 2 oddCoefficient_mem
  have hp : 2 • mixedDatum.parity true = (0 : ZMod 2) := rfl
  have hs : (2 : ℕ).choose 2 • mixedDatum.parity true = (1 : ZMod 2) := rfl
  simpa only [hp, inductionUnitDotSign, hs, sign_one,
    koszulSign_zero_right, one_smul, neg_one_smul] using h

/-- The third odd signed dot has both signs; on an odd coefficient they
cancel. This checks the comparison at a genuinely higher exponent. -/
example : signedMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 3 =
    coefficientMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 3 := by
  have h := signedMoment_coefficientMoment mixedDatum mixedScalars cutoff true
    (by decide) 3 oddCoefficient_mem
  have hp : 3 • mixedDatum.parity true = (1 : ZMod 2) := rfl
  have hs : (3 : ℕ).choose 2 • mixedDatum.parity true = (1 : ZMod 2) := rfl
  simpa only [hp, inductionUnitDotSign, hs, sign_one, koszulSign_one_one,
    neg_smul, one_smul, neg_one_smul, neg_neg] using h

/-- For the even moving colour the same odd coefficient remains present
and no signed-dot correction appears. -/
example : signedMoment mixedDatum mixedScalars cutoff false (by decide) oddCoefficient 3 =
    coefficientMoment mixedDatum mixedScalars cutoff false (by decide) oddCoefficient 3 := by
  have h := signedMoment_coefficientMoment mixedDatum mixedScalars cutoff false
    (by decide) 3 oddCoefficient_mem
  have hp : 3 • mixedDatum.parity false = (0 : ZMod 2) := rfl
  have hs : (3 : ℕ).choose 2 • mixedDatum.parity false = (0 : ZMod 2) := rfl
  simpa only [hp, inductionUnitDotSign, hs, sign_zero,
    koszulSign_zero_right, one_smul] using h

/-- The high raw moment retains the odd inverse-row superlinearity;
its coefficient is moved with an explicit minus sign. -/
example : coefficientMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 3 =
    -(oldComp mixedDatum mixedScalars cutoff [] [] []
      (coefficientMoment mixedDatum mixedScalars cutoff true (by decide) 1 3)
      (emptyCoefficient mixedDatum mixedScalars cutoff oddCoefficient)) := by
  have h := coefficientMoment_coefficient mixedDatum mixedScalars cutoff true
    (by decide) 3 oddCoefficient_mem
  have hp : (cutoff true - 1) • mixedDatum.parity true = (1 : ZMod 2) := rfl
  simpa only [hp, koszulSign_one_one, neg_smul, one_smul] using h

/-- The constructed signed moments satisfy the actual cyclotomic
recurrence at a nonzero shift for both moving parities. -/
example (i : Bool) :
    (∑ j : Fin (cutoff i + 1),
      koszulSign ((cutoff i : ZMod 2) * mixedDatum.parity i - j.val • mixedDatum.parity i)
        ((j.val + 1) • mixedDatum.parity i) •
      (inductionUnitDotSign (k := ℚ) (mixedDatum.parity i) (j.val + 1) •
        signedMoment mixedDatum mixedScalars cutoff i (by change 0 < 2; decide)
          (singleCoefficient mixedDatum cutoff i j) (j.val + 1))) = 0 :=
  signedMoment_recurrence mixedDatum mixedScalars cutoff i (by change 0 < 2; decide) 1

end NonVacuity.ELVVacuumSignedMoments

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSignedMoments | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"

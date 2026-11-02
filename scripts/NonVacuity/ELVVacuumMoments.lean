import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumMoments
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.VacuumCoefficient
open CyclotomicAction.AsymmetricParameters
namespace NonVacuity.ELVVacuumMoments

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

/-- In the actual odd old one-strand quotient at cutoff two, the full
exterior coefficient contributes the negative raw-coefficient sign. -/
example : coefficientMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 1 =
    -(emptyCoefficient mixedDatum mixedScalars cutoff oddCoefficient) := by
  have h := coefficientMoment_window mixedDatum mixedScalars cutoff true
    (by decide) 1 (by decide) oddCoefficient_mem
  have hp : 1 • mixedDatum.parity true = (1 : ZMod 2) := rfl
  simpa only [hp, koszulSign_one_one, inductionUnitDotSign, Nat.choose_self,
    Nat.choose_eq_zero_of_lt (by decide : 1 < 2), zero_nsmul, sign_zero,
    cutoff, Nat.reduceAdd, ↓reduceIte, one_smul, neg_smul] using h

/-- The same old exterior coefficient has no moving-dot Koszul sign for
the even colour, even though the coefficient itself remains odd. -/
example : coefficientMoment mixedDatum mixedScalars cutoff false (by decide) oddCoefficient 1 =
    emptyCoefficient mixedDatum mixedScalars cutoff oddCoefficient := by
  have h := coefficientMoment_window mixedDatum mixedScalars cutoff false
    (by decide) 1 (by decide) oddCoefficient_mem
  have hp : 1 • mixedDatum.parity false = (0 : ZMod 2) := rfl
  simpa only [hp, koszulSign_zero_right, inductionUnitDotSign,
    Nat.choose_eq_zero_of_lt (by decide : 1 < 2), zero_nsmul, sign_zero,
    cutoff, Nat.reduceAdd, ↓reduceIte, one_smul] using h

/-- The undotted raw coefficient is killed, rather than being discarded
by any specialization of the exterior algebra. -/
example : coefficientMoment mixedDatum mixedScalars cutoff true (by decide) oddCoefficient 0 = 0 := by
  have h := coefficientMoment_window mixedDatum mixedScalars cutoff true
    (by decide) 0 (by decide) oddCoefficient_mem
  have hz : (0 + 1 : ℕ) ≠ cutoff true := by decide
  rw [ite_eq_right hz, smul_zero, smul_zero] at h
  exact h

/-- An actual higher moment is solved from the literal monic old relation,
with the two coefficient products in their original left order. -/
example (i : Bool)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) mixedDatum cutoff) :
    coefficientMoment mixedDatum mixedScalars cutoff i (by change 0 < 2; decide) a 3 =
      -(coefficientMoment mixedDatum mixedScalars cutoff i (by change 0 < 2; decide)
          (a * singleCoefficient mixedDatum cutoff i (0 : Fin 2).castSucc) 1 +
        coefficientMoment mixedDatum mixedScalars cutoff i (by change 0 < 2; decide)
          (a * singleCoefficient mixedDatum cutoff i (1 : Fin 2).castSucc) 2) := by
  have h := coefficientMoment_leading mixedDatum mixedScalars cutoff i (by change 0 < 2; decide) a 1
  change coefficientMoment mixedDatum mixedScalars cutoff i _ a 3 =
    -(∑ j : Fin 2, coefficientMoment mixedDatum mixedScalars cutoff i _
      (a * singleCoefficient mixedDatum cutoff i j.castSucc) (j.val + 1)) at h
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.reduceAdd] using h

/-- At cutoff three the top signed dot has a nontrivial triangular sign,
even on the even unit coefficient. -/
example :
    let c3 := fun _ : Bool => 3
    coefficientMoment mixedDatum mixedScalars c3 true (by decide) 1 2 =
      -(emptyCoefficient mixedDatum mixedScalars c3 1) := by
  dsimp only
  let c3 := fun _ : Bool => 3
  have ha : (1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) mixedDatum c3) ∈
      SKM.SYM.elvCoefficientParity mixedDatum c3 0 := SetLike.GradedOne.one_mem
  have h := coefficientMoment_window mixedDatum mixedScalars c3 true
    (by decide) 2 (by decide) ha
  have hp : (2 : ℕ).choose 2 • mixedDatum.parity true = (1 : ZMod 2) := rfl
  have he : (2 + 1 : ℕ) = c3 true := rfl
  simpa only [inductionUnitDotSign, hp, koszulSign_zero_left,
    sign_one, he, ↓reduceIte, one_smul, neg_one_smul] using h

end NonVacuity.ELVVacuumMoments

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumMoments | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"

import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance

/-! # Vacuum coefficient moments in the one-strand quotient

The coefficient functional constructed from the unit inverse is transported
through the canonical upper-Hom equivalence. Its low output-polynomial
window and the actual full-coefficient cyclotomic recurrence give the
inputs to `SwappedVacuumNonpositiveBubbles.md`, §§2–4. No monic-basis or
annihilating-polynomial hypothesis is added.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The constructed vacuum functional in the literal one-strand old Hom,
using the canonical balanced-induction/representable comparison. -/
def upperFunctional (i : I) (hN : 0 < cutoff i) :
    Old D Sc cutoff [i] [i] →ₗ[k] Old D Sc cutoff [] [] :=
  (functional D Sc cutoff i hN).comp
    (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨[]⟩ : OldCategory D Sc cutoff) (⟨[]⟩ : OldCategory D Sc cutoff)).symm.toLinearMap

/-- The canonical comparison retains the prescribed signed-dot window on
every full old coefficient, with both moving parities included. -/
theorem upperFunctional_column (i : I) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) (b : Old D Sc cutoff [] []) :
    upperFunctional D Sc cutoff i hN
      (inductionUnitDotColumn D Sc cutoff i [] [] n b) =
      if n + 1 = cutoff i then b else 0 := by
  rw [inductionUnitDotColumn_categorical]
  change functional D Sc cutoff i hN
    ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨[]⟩ : OldCategory D Sc cutoff) (⟨[]⟩ : OldCategory D Sc cutoff)).symm
      ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i
        (⟨[]⟩ : OldCategory D Sc cutoff) (⟨[]⟩ : OldCategory D Sc cutoff)) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  have h := functional_dot_window D Sc cutoff i hN n hn b
  rw [Module.End.pow_apply] at h
  exact h

/-- In raw output-polynomial coordinates, the triangular odd dot-power
scalar remains visible. This includes arbitrary exterior coefficients. -/
theorem upperFunctional_output_window (i : I) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) (b : Old D Sc cutoff [] []) :
    upperFunctional D Sc cutoff i hN
      (canonicalAppendTarget D Sc cutoff i [] [i]
        (appendOutputEmbedding D Sc cutoff i [] [] (Finsupp.single n b))) =
      inductionUnitDotSign (k := k) (D.parity i) n •
        (if n + 1 = cutoff i then b else 0) := by
  have h := upperFunctional_column D Sc cutoff i hN n hn b
  rw [inductionUnitDotColumn_apply, map_smul] at h
  have hs := congrArg (fun z : Old D Sc cutoff [] [] =>
    inductionUnitDotSign (k := k) (D.parity i) n • z) h
  simpa only [List.nil_append, smul_smul, inductionUnitDotSign,
    Supercategory.sign_mul_self, one_smul] using hs

/-- A full ELV coefficient at the empty old word. -/
def emptyCoefficient (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Old D Sc cutoff [] [] :=
  (ideal D Sc cutoff [] []).mkQ (ELVPScalar.scalar D Sc cutoff [] a)

/-- Moving a coefficient from the output-polynomial position to the
coefficient-left raw monomial introduces its full Koszul sign. -/
theorem output_monomial (i : I) (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    canonicalAppendTarget D Sc cutoff i [] [i]
      (appendOutputEmbedding D Sc cutoff i [] []
        (Finsupp.single n (emptyCoefficient D Sc cutoff a))) =
      koszulSign p (n • D.parity i) • singleClass D Sc cutoff i a n := by
  rw [emptyCoefficient, appendOutputEmbedding_single]
  simp only [List.nil_append] at *
  change (ideal D Sc cutoff [i] [i]).mkQ
    (rightContext D Sc cutoff [i] [] [] (ELVPScalar.scalar D Sc cutoff [] a) ≫
      appendMovingPower D Sc cutoff i [] n) = _
  rw [ELVPScalar.rightContext_scalar]
  simp only [List.nil_append]
  have he : ELVPScalar.scalar D Sc cutoff [i] a ≫
      appendMovingPower D Sc cutoff i [] n =
      koszulSign p (n • D.parity i) • singleTerm D Sc cutoff i a n := by
    change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
      a (𝟙 _) ≫ BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
        (𝟙 _) (dotE D Sc [i] 0 ^ n) = _
    rw [BoxProd.tmulHom_comp_tmulHom ha (𝟙 _) (𝟙 _)
      (firstDot_pow_parity D Sc i [] n)]
    simp only [Category.comp_id, Category.id_comp]
    rfl
  rw [he, map_zsmul]
  rfl

/-- Coefficient-left moments of the actual one-strand quotient. Coefficient
order is retained rather than replaced by an unsigned scalar action. -/
def coefficientMoment (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    Old D Sc cutoff [] [] :=
  upperFunctional D Sc cutoff i hN (singleClass D Sc cutoff i a n)

/-- The complete low raw-monomial window. Besides the triangular dot-power
sign, odd coefficients contribute the required coefficient-order sign. -/
theorem coefficientMoment_window (i : I) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    coefficientMoment D Sc cutoff i hN a n =
      koszulSign p (n • D.parity i) •
        (inductionUnitDotSign (k := k) (D.parity i) n •
          (if n + 1 = cutoff i then emptyCoefficient D Sc cutoff a else 0)) := by
  have h := upperFunctional_output_window D Sc cutoff i hN n hn
    (emptyCoefficient D Sc cutoff a)
  rw [output_monomial D Sc cutoff i n ha, map_zsmul] at h
  have hs := congrArg (fun z : Old D Sc cutoff [] [] =>
    koszulSign p (n • D.parity i) • z) h
  simpa only [smul_smul, koszulSign_mul_self, one_smul, coefficientMoment] using hs

/-- The actual old relation determines all higher coefficient-left
moments, with its original coefficient order and signs. -/
theorem coefficientMoment_recurrence (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1), coefficientMoment D Sc cutoff i hN
      (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 := by
  have h := congrArg (upperFunctional D Sc cutoff i hN)
    (single_recurrence D Sc cutoff i a m)
  simpa only [map_sum, map_zero, coefficientMoment] using h

/-- Solving the monic leading term gives a terminating recurrence; every
exponent on the right is strictly smaller than `cutoff i + m`. -/
theorem coefficientMoment_leading (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ) :
    coefficientMoment D Sc cutoff i hN a (cutoff i + m) =
      -(∑ j : Fin (cutoff i), coefficientMoment D Sc cutoff i hN
        (a * singleCoefficient D cutoff i j.castSucc) (j.val + m)) := by
  have h := coefficientMoment_recurrence D Sc cutoff i hN a m
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.val_last, singleCoefficient_top, mul_one] at h
  exact eq_neg_of_add_eq_zero_right h

end OddMath.QuiverHecke.ELVOld.VacuumCoefficient

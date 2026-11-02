import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicTransport

/-! # Signed higher dots on the old vacuum

The signed right-dot comparison in `SwappedVacuumNonpositiveBubbles.md`,
§2 is attached to the constructed induction dot and coefficient functional,
at every exponent, rather than identifying an ordinary right composition
with a supernatural map.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumCoefficient
open CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- An actual signed-dot/ordinary-unit moment, on the full coefficient
class at the empty old word. -/
def signedMoment (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    Old D Sc cutoff [] [] :=
  functional D Sc cutoff i hN
    (((actualInductionDot D Sc cutoff i (coefficientModule D Sc cutoff)
      ((append D Sc cutoff i).obj ⟨[]⟩)) ^ n)
      ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
        (coefficientModule D Sc cutoff)).total ⟨[]⟩)
          (emptyCoefficient D Sc cutoff a)))

/-- The canonical upper-Hom comparison identifies every signed-dot
moment with the literal categorical column, without an exponent bound. -/
theorem signedMoment_column (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    signedMoment D Sc cutoff i hN a n =
      upperFunctional D Sc cutoff i hN
        (inductionUnitDotColumn D Sc cutoff i [] [] n (emptyCoefficient D Sc cutoff a)) := by
  rw [inductionUnitDotColumn_categorical]
  change _ = functional D Sc cutoff i hN
    ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨[]⟩ : OldCategory D Sc cutoff) (⟨[]⟩ : OldCategory D Sc cutoff)).symm
      ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i
        (⟨[]⟩ : OldCategory D Sc cutoff) (⟨[]⟩ : OldCategory D Sc cutoff)) _))
  rw [LinearEquiv.symm_apply_apply]
  unfold signedMoment
  rw [Module.End.pow_apply]
  rfl

/-- The signed-power and coefficient-order scalars relate actual higher
signed-dot moments to the raw monomial moments satisfying the literal
cyclotomic recurrence. This holds at every exponent. -/
theorem signedMoment_coefficientMoment (i : I) (hN : 0 < cutoff i)
    (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    signedMoment D Sc cutoff i hN a n =
      inductionUnitDotSign (k := k) (D.parity i) n •
        (koszulSign p (n • D.parity i) • coefficientMoment D Sc cutoff i hN a n) := by
  rw [signedMoment_column, inductionUnitDotColumn_apply]
  simp only [List.nil_append]
  rw [map_smul]
  have h := congrArg (upperFunctional D Sc cutoff i hN)
    (output_monomial D Sc cutoff i n ha)
  rw [map_zsmul] at h
  exact congrArg (fun z : Old D Sc cutoff [] [] =>
    inductionUnitDotSign (k := k) (D.parity i) n • z) h

/-- The inverse comparison: raw moments are recovered from the actual
signed moments with the same involutive scalars. -/
theorem coefficientMoment_signedMoment (i : I) (hN : 0 < cutoff i)
    (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    coefficientMoment D Sc cutoff i hN a n =
      koszulSign p (n • D.parity i) •
        (inductionUnitDotSign (k := k) (D.parity i) n • signedMoment D Sc cutoff i hN a n) := by
  rw [signedMoment_coefficientMoment D Sc cutoff i hN n ha]
  simp only [smul_smul, inductionUnitDotSign, Supercategory.sign_mul_self,
    koszulSign_mul_self, one_smul]

/-- The constructed vacuum functional is supernatural against every
homogeneous empty-word endomorphism, including odd exterior coefficients. -/
theorem functional_end_naturality (i : I) (hN : 0 < cutoff i) {q : ZMod 2}
    (f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩)
    (hf : f ∈ parity (R := k) (⟨[]⟩ : OldCategory D Sc cutoff) ⟨[]⟩ q) :
    (functional D Sc cutoff i hN).comp
      (SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          (coefficientModule D Sc cutoff))).map f)) =
      koszulSign ((cutoff i - 1) • D.parity i) q •
        ((SVec.toLinearMap ((coefficientModule D Sc cutoff).map f)).comp
          (functional D Sc cutoff i hN)) := by
  unfold functional
  exact moduleUnitCoefficient_end_naturality D Sc cutoff
    (coefficientModule D Sc cutoff) i ⟨[]⟩ _ _ f hf

/-- The same full-coefficient sign in literal upper-Hom coordinates.
The canonical upper-Hom inverse is natural, so transporting the chosen
inverse row does not add a coefficient rescaling. -/
theorem upperFunctional_end_naturality (i : I) (hN : 0 < cutoff i) {q : ZMod 2}
    (f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩)
    (hf : f ∈ parity (R := k) (⟨[]⟩ : OldCategory D Sc cutoff) ⟨[]⟩ q)
    (z : Old D Sc cutoff [i] [i]) :
    upperFunctional D Sc cutoff i hN (oldComp D Sc cutoff [i] [i] [i]
      z ((append D Sc cutoff i).map (X := ⟨[]⟩) (Y := ⟨[]⟩) f)) =
      koszulSign ((cutoff i - 1) • D.parity i) q •
        oldComp D Sc cutoff [] [] [] (upperFunctional D Sc cutoff i hN z) f := by
  let w : OldCategory D Sc cutoff := ⟨[]⟩
  let J := append D Sc cutoff i
  let B := OldInductionRepresentable.backward D Sc cutoff i w (J.obj w)
  have hb := LinearMap.congr_fun
    (OldInductionRepresentable.backward_naturality D Sc cutoff i w
      (J.map (X := w) (Y := w) f)) z
  change B (z ≫ J.map (X := w) (Y := w) f) = BalancedInduction.postcompose J
    (oldRepresentableFunctor D Sc cutoff w) (J.map (X := w) (Y := w) f) (B z) at hb
  have h := LinearMap.congr_fun (functional_end_naturality D Sc cutoff i hN f hf) (B z)
  change functional D Sc cutoff i hN
      (BalancedInduction.postcompose J (oldRepresentableFunctor D Sc cutoff w)
        (J.map (X := w) (Y := w) f) (B z)) =
    koszulSign ((cutoff i - 1) • D.parity i) q •
      (functional D Sc cutoff i hN (B z) ≫ f) at h
  change functional D Sc cutoff i hN (B (z ≫ J.map (X := w) (Y := w) f)) = _
  exact (congrArg (functional D Sc cutoff i hN) hb).trans h

private theorem singleClass_postcompose (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    oldComp D Sc cutoff [i] [i] [i] (singleClass D Sc cutoff i 1 n)
      ((append D Sc cutoff i).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (emptyCoefficient D Sc cutoff a)) = singleClass D Sc cutoff i a n := by
  change oldComp D Sc cutoff [i] [i] [i]
    ((ideal D Sc cutoff [i] [i]).mkQ (singleTerm D Sc cutoff i 1 n))
    ((ideal D Sc cutoff [i] [i]).mkQ
      (rightContext D Sc cutoff [i] [] [] (ELVPScalar.scalar D Sc cutoff [] a))) = _
  rw [oldComp_mk, ELVPScalar.rightContext_scalar]
  simp only [List.nil_append]
  congr 1
  change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
    (𝟙 _) (dotE D Sc [i] 0 ^ n) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i]) a (𝟙 _) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [proj_id, ↓reduceIte, one_ne_zero, Category.id_comp, Limits.zero_comp,
    BoxProd.tmulHom_def, TensorProduct.zero_tmul, Category.comp_id, add_zero]

/-- The higher raw moment has the same full-coefficient superlinearity as
the constructed inverse row. Multiplication is the literal empty-word
composition, so its coefficient order is explicit. -/
theorem coefficientMoment_coefficient (i : I) (hN : 0 < cutoff i)
    (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    coefficientMoment D Sc cutoff i hN a n =
      koszulSign ((cutoff i - 1) • D.parity i) p •
        oldComp D Sc cutoff [] [] [] (coefficientMoment D Sc cutoff i hN 1 n)
          (emptyCoefficient D Sc cutoff a) := by
  have hf : emptyCoefficient D Sc cutoff a ∈
      parity (R := k) (⟨[]⟩ : OldCategory D Sc cutoff) ⟨[]⟩ p := by
    exact Submodule.mem_map_of_mem (ELVPScalar.scalar_mem D Sc cutoff [] ha)
  have h := upperFunctional_end_naturality D Sc cutoff i hN
    (emptyCoefficient D Sc cutoff a) hf (singleClass D Sc cutoff i 1 n)
  rw [singleClass_postcompose D Sc cutoff i a n] at h
  exact h

/-- The actual full-coefficient cyclotomic recurrence expressed entirely
in signed-dot/ordinary-unit moments. The two displayed scalars are the
coefficient-order and signed-power corrections, respectively. -/
theorem signedMoment_recurrence (i : I) (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      koszulSign ((cutoff i : ZMod 2) * D.parity i - j.val • D.parity i)
        ((j.val + m) • D.parity i) •
      (inductionUnitDotSign (k := k) (D.parity i) (j.val + m) •
        signedMoment D Sc cutoff i hN (singleCoefficient D cutoff i j) (j.val + m))) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1), coefficientMoment D Sc cutoff i hN
        (singleCoefficient D cutoff i j) (j.val + m) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (coefficientMoment_signedMoment D Sc cutoff i hN (j.val + m)
        (singleCoefficient_mem D cutoff i j)).symm
    _ = 0 := by
      simpa only [one_mul] using coefficientMoment_recurrence D Sc cutoff i hN 1 m

end OddMath.QuiverHecke.ELVOld.VacuumCoefficient

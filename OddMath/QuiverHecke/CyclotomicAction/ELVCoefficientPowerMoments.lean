import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRows
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance

/-! # One-strand moments on the literal coefficient-power vacuum

The coefficient-extraction input of `SwappedVacuumNonpositiveBubbles.md`,
§§2–4, is evaluated on the regular A/T old vacuum. The literal one-strand
cyclotomic relation determines its higher moments; no relation or extractor
is supplied as an additional hypothesis.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The actual coend generator at the chosen vacuum vector, linear in
the complete one-strand old Hom, including exterior coefficients. -/
def rawVector (i : I) : Old D Sc cutoff [i] [i] →ₗ[k]
    mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩ :=
  let J := append D Sc cutoff i
  let M := coefficientPowerVacuum D Sc cutoff L
  let w : OldCategory D Sc cutoff := ⟨[]⟩
  (BalancedInduction.inclusion J M.toFunctor (J.obj w) w).comp
    ((TensorProduct.mk k (J.obj w ⟶ J.obj w) (M.obj w)).flip
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1))

/-- The prescribed inverse row evaluated on literal one-strand old arrows. -/
def upperFunctional (i : I) (hN : 0 < cutoff i) :
    Old D Sc cutoff [i] [i] →ₗ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (functional D Sc cutoff L i hN).comp (rawVector D Sc cutoff L i)

/-- Coefficient-left raw moments of the actual power vacuum. -/
def rawMoment (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  upperFunctional D Sc cutoff L i hN (singleClass D Sc cutoff i a n)

/-- The actual one-strand relation determines higher raw moments in its
original coefficient order. -/
theorem rawMoment_recurrence (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1), rawMoment D Sc cutoff L i hN
      (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 := by
  have h := congrArg (upperFunctional D Sc cutoff L i hN)
    (single_recurrence D Sc cutoff i a m)
  simpa only [map_sum, map_zero, rawMoment] using h

/-- Signed higher moments on the ordinary unit of the same power vacuum. -/
def signedMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  functional D Sc cutoff L i hN
    ((inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      ((append D Sc cutoff i).obj ⟨[]⟩) ^ n) (unit D Sc cutoff L i 1))

/-- At every exponent the existing signed dot differs from the literal
raw monomial by exactly its triangular power scalar. -/
theorem signedMoment_rawMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    signedMoment D Sc cutoff L i hN n =
      inductionUnitDotSign (k := k) (D.parity i) n • rawMoment D Sc cutoff L i hN 1 n := by
  have h := inductionDot_iterate_unit D Sc cutoff i
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff) n
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1)
  rw [← Module.End.pow_apply] at h
  have hu := adjunctionUnit_total_apply D Sc cutoff i
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1)
  change (unit D Sc cutoff L i) 1 = _ at hu
  rw [← hu] at h
  have hv := congrArg (functional D Sc cutoff L i hN) h
  rw [map_smul] at hv
  exact hv

/-- The same involutive triangular scalar recovers the raw moment from
its signed-dot moment at every exponent. -/
theorem rawMoment_signedMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    rawMoment D Sc cutoff L i hN 1 n =
      inductionUnitDotSign (k := k) (D.parity i) n • signedMoment D Sc cutoff L i hN n := by
  rw [signedMoment_rawMoment]
  simp only [smul_smul, inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]

/-- The low raw scalar window follows from the prescribed inverse row
and the actual signed-dot power comparison. -/
theorem rawMoment_one_window (i : I) (hN : 0 < cutoff i) (n : ℕ) (hn : n < cutoff i) :
    rawMoment D Sc cutoff L i hN 1 n =
      inductionUnitDotSign (k := k) (D.parity i) n •
        (if n + 1 = cutoff i then 1 else 0) := by
  rw [rawMoment_signedMoment]
  have h := functional_dot_window D Sc cutoff L i hN n hn
    (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  change signedMoment D Sc cutoff L i hN n = _ at h
  rw [h]

private theorem singleClass_postcompose (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    (show End ((append D Sc cutoff i).obj (⟨[]⟩ : OldCategory D Sc cutoff)) from
      singleClass D Sc cutoff i 1 n) ≫
      ((append D Sc cutoff i).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a)) = singleClass D Sc cutoff i a n := by
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

/-- Raw higher moments retain the full inverse row's coefficient sign
and the original left multiplication order in literal A/T. -/
theorem rawMoment_coefficient (i : I) (hN : 0 < cutoff i) (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    rawMoment D Sc cutoff L i hN a n =
      koszulSign ((cutoff i - 1) • D.parity i) p •
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
          rawMoment D Sc cutoff L i hN 1 n) := by
  have h := functional_coefficient D Sc cutoff L i hN ha
    (rawVector D Sc cutoff L i (singleClass D Sc cutoff i 1 n))
  change functional D Sc cutoff L i hN
    (BalancedInduction.postcompose (append D Sc cutoff i)
      (coefficientPowerVacuum D Sc cutoff L).toFunctor
      ((append D Sc cutoff i).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a))
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
        (singleClass D Sc cutoff i 1 n) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1))) = _ at h
  rw [BalancedInduction.postcompose_tensor, singleClass_postcompose] at h
  exact h

/-- The actual monic relation expressed in scalar raw moments on A/T.
The coefficients remain on their proved left side, with the top-row sign. -/
theorem rawMoment_one_recurrence (i : I) (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      koszulSign ((cutoff i - 1) • D.parity i)
        ((cutoff i : ZMod 2) * D.parity i - j.val • D.parity i) •
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m))) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1), rawMoment D Sc cutoff L i hN
        (singleCoefficient D cutoff i j) (j.val + m) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (rawMoment_coefficient D Sc cutoff L i hN (j.val + m)
        (singleCoefficient_mem D cutoff i j)).symm
    _ = 0 := by
      simpa only [one_mul] using rawMoment_recurrence D Sc cutoff L i hN 1 m

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient

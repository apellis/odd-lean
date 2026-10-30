/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVQPBoundaryDivision
/-!
# Highest coefficient of the ordered reverse numerator

Support bounds and unit times identity at the prescribed degree of the explicit
ordered fold in `DeformedBoundaryDivision.md` (7). These statements allow zero
old endomorphism spaces: no nonzero leading coefficient is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem inputCoefficientShift_above (i : I) (v : List I) (d m n : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (hf : ∀ r, m < r → f r = 0)
    (hn : d + m < n) : inputCoefficientShift D Sc cutoff i v d f n = 0 := by
  rw [inputCoefficientShift_apply]
  apply Finset.sum_eq_zero
  intro r _
  split_ifs with h
  · rw [hf r (by omega), map_zero]
  · rfl

theorem inputCoefficientComp_apply (v : List I) (c : hom D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    inputCoefficientComp D Sc cutoff v c f n =
      oldComp D Sc cutoff v v v ((ideal D Sc cutoff v v).mkQ c) (f n) := rfl

theorem inputCoefficientShift_unit_top (i : I) (v : List I) (d m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (u : kˣ)
    (hf : f m = (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :
    inputCoefficientShift D Sc cutoff i v d f (d + m) =
      (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  rw [inputCoefficientShift_apply_add, hf, map_smul]
  change (u : k) • (ideal D Sc cutoff v v).mkQ (twist k _ (𝟙 _)) = _
  rw [twist_id]

theorem endpointOutputCoefficients_above (i : I) (v : List I) (n : ℕ)
    (hn : cutoff i < n) : endpointOutputCoefficients D Sc cutoff i v n = 0 := by
  simp only [endpointOutputCoefficients, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  exact Finsupp.single_eq_of_ne (by omega)

theorem endpointOutputCoefficients_top (i : I) (v : List I) :
    endpointOutputCoefficients D Sc cutoff i v (cutoff i) =
      (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  unfold endpointOutputCoefficients
  rw [Fin.sum_univ_castSucc]
  simp only [Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hz : (∑ a : Fin (cutoff i),
      (Finsupp.single a.val ((ideal D Sc cutoff v v).mkQ
        (twist k (a.val • D.parity i)
          (ELVPScalar.scalar D Sc cutoff v (singleCoefficient D cutoff i a.castSucc)))))
      (cutoff i)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact Finsupp.single_eq_of_ne (by omega)
  simp only [Fin.val_castSucc]
  rw [hz]
  simp only [zero_add, Fin.val_last, Finsupp.single_eq_same, singleCoefficient_top]
  change (ideal D Sc cutoff v v).mkQ (twist k _ (𝟙 _)) = _
  rw [twist_id]

theorem qpOutputCoefficientStep_above (i : I) (v : List I) (b m n : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (hf : ∀ r, m < r → f r = 0)
    (hn : appendQPDegree D i (v.getD b i) + m < n) :
    qpOutputCoefficientStep D Sc cutoff i v b f n = 0 := by
  have ho (a r : ℕ) (hr : m < r) :
      inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a) f r = 0 := by
    rw [inputCoefficientComp_apply, hf r hr, map_zero]
  have ht (e : ℕ) (he : e + m < n) :=
    inputCoefficientShift_above D Sc cutoff i v e m n f hf he
  unfold qpOutputCoefficientStep
  dsimp only
  split_ifs with hj hp hd
  · simp only [appendQPDegree, hj, hp, ↓reduceIte] at hn
    simp only [Finsupp.add_apply, ho 2 n (by omega), ht 2 hn, add_zero]
  · simp only [appendQPDegree, hj, hp, ↓reduceIte, zero_add] at hn
    simp only [Finsupp.neg_apply, hf n hn, neg_zero]
  · have hd0 : D.dn i (v.getD b i) = 0 := by
      have H := D.dn_cast (Ne.symm hj)
      omega
    simp only [appendQPDegree, hj, ↓reduceIte, hd0, zero_add] at hn
    simp only [Finsupp.smul_apply, hf n hn, smul_zero]
  · simp only [appendQPDegree, hj, ↓reduceIte] at hn
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    have hs : (∑ e ∈ Finset.Ioo 0 (D.dn i (v.getD b i)),
        ∑ a ∈ Finset.Ioo 0 (D.dn (v.getD b i) i),
          Sc.s i (v.getD b i) e a •
            inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a)
              (inputCoefficientShift D Sc cutoff i v e f) n) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro a _
      rw [inputCoefficientComp_apply, ht e (by have := (Finset.mem_Ioo.mp he).2; omega),
        map_zero, smul_zero]
    rw [hs, ht _ hn, ho _ n (by omega), smul_zero, smul_zero, add_zero, add_zero]

theorem qpOutputCoefficientStep_unit_top (i : I) (v : List I) (b m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (u : kˣ)
    (hf : ∀ r, m < r → f r = 0)
    (htop : f m = (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :
    qpOutputCoefficientStep D Sc cutoff i v b f (appendQPDegree D i (v.getD b i) + m) =
      ((appendQPUnit D Sc i (v.getD b i) * u : kˣ) : k) •
        (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have ho (a n : ℕ) (hn : m < n) :
      inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a) f n = 0 := by
    rw [inputCoefficientComp_apply, hf n hn, map_zero]
  have ht (e : ℕ) := inputCoefficientShift_unit_top D Sc cutoff i v e m f u htop
  unfold qpOutputCoefficientStep appendQPDegree appendQPUnit
  dsimp only
  split_ifs with hj hp hd
  · simp only [Finsupp.add_apply, ho 2 (2 + m) (by omega), ht, zero_add,
      one_mul]
  · simp only [zero_add, Finsupp.neg_apply, htop, Units.val_neg,
      neg_one_mul, neg_smul]
  · have hd0 : D.dn i (v.getD b i) = 0 := by
      have H := D.dn_cast (Ne.symm hj)
      omega
    simp only [hd0, zero_add, Finsupp.smul_apply, htop, smul_smul, Units.val_mul]
  · have hdpos : 0 < D.dn i (v.getD b i) := by
      have H := D.dn_cast (Ne.symm hj)
      omega
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    have hs : (∑ e ∈ Finset.Ioo 0 (D.dn i (v.getD b i)),
        ∑ a ∈ Finset.Ioo 0 (D.dn (v.getD b i) i),
          Sc.s i (v.getD b i) e a •
            inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a)
              (inputCoefficientShift D Sc cutoff i v e f) (D.dn i (v.getD b i) + m)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro a _
      rw [inputCoefficientComp_apply,
        inputCoefficientShift_above D Sc cutoff i v e m _ f hf
          (by have := (Finset.mem_Ioo.mp he).2; omega), map_zero, smul_zero]
    rw [hs, ht, ho _ _ (by omega), smul_zero, add_zero, zero_add, smul_smul]
    rfl

theorem orderedQPOutputCoefficients_above (i : I) (v : List I)
    (l : List ℕ) (m : ℕ) (f : ℕ →₀ Old D Sc cutoff v v)
    (hf : ∀ r, m < r → f r = 0) (n : ℕ)
    (hn : (l.map (fun b => appendQPDegree D i (v.getD b i))).sum + m < n) :
    orderedQPOutputCoefficients D Sc cutoff i v l f n = 0 := by
  induction l generalizing m f with
  | nil => exact hf n (by simpa using hn)
  | cons b l ih =>
    apply ih (appendQPDegree D i (v.getD b i) + m) _
      (fun r hr => qpOutputCoefficientStep_above D Sc cutoff i v b m r f hf hr)
    simp only [List.map_cons, List.sum_cons] at hn
    omega

theorem orderedQPOutputCoefficients_unit_top (i : I) (v : List I)
    (l : List ℕ) (m : ℕ) (f : ℕ →₀ Old D Sc cutoff v v) (u : kˣ)
    (hf : ∀ r, m < r → f r = 0)
    (htop : f m = (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :
    orderedQPOutputCoefficients D Sc cutoff i v l f
      ((l.map (fun b => appendQPDegree D i (v.getD b i))).sum + m) =
      (((l.map (fun b => appendQPUnit D Sc i (v.getD b i))).prod * u : kˣ) : k) •
        (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  induction l generalizing m f u with
  | nil => simpa only [orderedQPOutputCoefficients, List.foldl_nil, List.map_nil,
      List.sum_nil, List.prod_nil, zero_add, one_mul] using htop
  | cons b l ih =>
    have H := ih (appendQPDegree D i (v.getD b i) + m)
      (qpOutputCoefficientStep D Sc cutoff i v b f) (appendQPUnit D Sc i (v.getD b i) * u)
      (fun r hr => qpOutputCoefficientStep_above D Sc cutoff i v b m r f hf hr)
      (qpOutputCoefficientStep_unit_top D Sc cutoff i v b m f u hf htop)
    simpa only [orderedQPOutputCoefficients, List.foldl_cons, List.map_cons,
      List.sum_cons, List.prod_cons, Nat.add_assoc, Nat.add_left_comm,
      mul_assoc, mul_left_comm] using H

/-- Bounded support of the literal ordered reverse-numerator fold. -/
theorem orderedReverseNumerator_above (i : I) (v : List I) (n : ℕ)
    (hn : endpointQPDegree D cutoff i v < n) :
    orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
      (endpointOutputCoefficients D Sc cutoff i v) n = 0 := by
  apply orderedQPOutputCoefficients_above D Sc cutoff i v _ (cutoff i) _
    (endpointOutputCoefficients_above D Sc cutoff i v) n
  simpa only [endpointQPDegree, Nat.add_comm] using hn

/-- The coefficient at the prescribed bound is a scalar unit times the old
identity, even when that identity vanishes. This is not a nonzero-degree claim. -/
theorem orderedReverseNumerator_top (i : I) (v : List I) :
    orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
      (endpointOutputCoefficients D Sc cutoff i v) (endpointQPDegree D cutoff i v) =
      (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have H := orderedQPOutputCoefficients_unit_top D Sc cutoff i v
    (List.range v.length) (cutoff i) (endpointOutputCoefficients D Sc cutoff i v) 1
    (endpointOutputCoefficients_above D Sc cutoff i v)
    (by simpa only [Units.val_one, one_smul] using endpointOutputCoefficients_top D Sc cutoff i v)
  simpa only [endpointQPDegree, appendQPProductUnit, mul_one, Nat.add_comm] using H

theorem orderedReverseNumerator_support (i : I) (v : List I) :
    (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
      (endpointOutputCoefficients D Sc cutoff i v)).support ⊆
        Finset.range (endpointQPDegree D cutoff i v + 1) := by
  intro n hn
  apply Finset.mem_range.mpr
  by_contra h
  exact (Finsupp.mem_support_iff.mp hn)
    (orderedReverseNumerator_above D Sc cutoff i v n (by omega))

/-- The concrete reverse numerator at every input power retains its unit top
coefficient: the total coefficient twist fixes the scalar identity. -/
theorem appendC0_orderedReverseNumerator_top (i : I) (v : List I) (d : ℕ) :
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v))
      (d + endpointQPDegree D cutoff i v) =
      (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  rw [appendC0_orderedReverseNumerator]
  exact inputCoefficientShift_unit_top D Sc cutoff i v d _ _ _
    (orderedReverseNumerator_top D Sc cutoff i v)

theorem appendC0_orderedReverseNumerator_above (i : I) (v : List I) (d n : ℕ)
    (hn : d + endpointQPDegree D cutoff i v < n) :
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v)) n = 0 := by
  rw [appendC0_orderedReverseNumerator]
  exact inputCoefficientShift_above D Sc cutoff i v d _ n _
    (orderedReverseNumerator_above D Sc cutoff i v) hn

end OddMath.QuiverHecke.ELVOld

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideInduction
/-!
# General connected bubble slides

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 7.3(iii), (7.11)–(7.12), for all weights and integer shifted
degrees, including fake bubbles. The full rectangular polynomial is retained.

The middle-weight proof uses the dotted recurrence and coefficient induction.
The outer weight ranges use the corresponding natural-dot slide and the
actual inverse bubble series. The signed normalization is cancelled only after
using the original scalar parity conditions. No nondegeneracy is asserted.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

def bubbleSlideRHSR (i j : I) (μ : X) (n : ℤ) :=
  (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) n) +
  (Sc.t j i : k) • (lbub j μ (bubRs cs i (wt D μ [up j]) (n - D.dn i j)) ≫
    cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))) +
  ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
    Sc.s i j p q • (lbub j μ (bubRs cs i (wt D μ [up j]) (n + p - D.dn i j)) ≫
      cl D Sc μ [up j] [up j] (dotsL [] j [] q))

def bubbleSlideRHSL (i j : I) (μ : X) (n : ℤ) :=
  (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) +
  (Sc.t j i : k) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
    rbub j μ (bubLs cs i (wt D μ []) (n - D.dn i j))) +
  ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
    Sc.s i j p q • (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      rbub j μ (bubLs cs i (wt D μ []) (n + p - D.dn i j)))

theorem bubbleR_polynomial_natural_shift (i j : I) (μ : X) (hij : i ≠ j)
    (hd : D.d i j ≠ 0) (n : ℤ) (hn : D.h i μ < n) :
    rbub j μ (bubRs cs i (wt D μ []) n) = bubbleSlideRHSR cs i j μ n := by
  have H := bubbleR_slide_polynomial_raw cs i j μ hij hd (n - D.h i μ - 1).toNat
  have ha : ((n - D.h i μ - 1).toNat : ℤ) = n - D.h i μ - 1 := Int.toNat_of_nonneg (by omega)
  have he := D.dn_cast hij
  simp only [ha] at H
  simp only [bubbleSlideRHSR, bubRs, h_wt_upj, wt_nil]
  simp only [bubbleR_right, bubbleR_left, wt_nil, he] at H
  simp only [he]
  ring_nf at H ⊢
  exact H

theorem bubbleL_polynomial_natural_shift (i j : I) (μ : X) (hij : i ≠ j)
    (hd : D.d i j ≠ 0) (n : ℤ) (hn : D.d i j - D.h i μ < n) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) = bubbleSlideRHSL cs i j μ n := by
  have H := bubbleL_slide_polynomial_raw cs i j μ hij hd (n + D.h i μ - D.d i j - 1).toNat
  have ha : ((n + D.h i μ - D.d i j - 1).toNat : ℤ) = n + D.h i μ - D.d i j - 1 := Int.toNat_of_nonneg (by omega)
  have he := D.dn_cast hij
  simp only [ha] at H
  simp only [bubbleSlideRHSL, bubLs, h_wt_upj, wt_nil]
  simp only [bubbleL_right, bubbleL_left, wt_nil, he] at H
  simp only [he]
  ring_nf at H ⊢
  exact H
theorem bubbleSlideMonomial_sum_right (j : I) (μ : X) (d q n : ℕ) (a : k)
    (B : ℕ → ((pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j]))) :
    (∑ r ∈ range (n + 1), B (n - r) ≫ bubbleSlideMonomial (Sc := Sc) j μ d q a r) =
    a • (if d ≤ n then B (n - d) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) else 0) := by
  simp [bubbleSlideMonomial, comp_ite, Linear.comp_smul, mem_range, smul_ite]

theorem bubblePolynomialCoeff_conv_right (i j : I) (μ : X) (hd : 0 < D.dn i j) (n : ℕ)
    (B : ℕ → ((pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j]))) :
    bubbleConvolution B (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ) n =
    B n + ((↑(Sc.t i j)⁻¹ : k) * (Sc.t j i : k)) •
      (if D.dn i j ≤ n then B (n - D.dn i j) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) else 0) +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      ((↑(Sc.t i j)⁻¹ : k) * Sc.s i j p q) • (if D.dn i j - p ≤ n then
        B (n - (D.dn i j - p)) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) else 0) := by
  rw [bubbleConvolution]
  simp only [bubbleSlidePolynomialCoeff_add i j μ hd, Preadditive.comp_add, Preadditive.comp_sum, sum_add_distrib]
  rw [sum_comm (s := range (n + 1)) (t := Ioo 0 (D.dn i j))]
  simp_rw [sum_comm (s := range (n + 1)) (t := Ioo 0 (D.dn j i)), bubbleSlideMonomial_sum_right]
  simp [comp_ite]

theorem bubbleR_conv_normalize (i j : I) (μ : X) (hd : 0 < D.dn i j) (n : ℕ) :
    bubbleConvolution (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
      (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ) n =
    (cs.c μ i : k) • bubbleSlideRHSR cs i j μ n := by
  rw [bubblePolynomialCoeff_conv_right i j μ hd]
  simp only [bubbleSlideRHSR, bubbleCoeffR, lbub, map_smul, Linear.smul_comp,
    smul_add, smul_sum, smul_smul, c_wt_upj, Units.val_mul]
  have ht (a : k) : ((↑(Sc.t i j)⁻¹ : k) * a) * ((cs.c μ i : k) * (Sc.t i j : k)) =
      (cs.c μ i : k) * a := by
    calc
      _ = ((↑(Sc.t i j)⁻¹ : k) * (Sc.t i j : k)) * ((cs.c μ i : k) * a) := by ring
      _ = _ := by rw [Units.inv_mul, one_mul]
  have hterm (d q : ℕ) (a : k) :
      ((↑(Sc.t i j)⁻¹ : k) * a) •
        (if d ≤ n then ((cs.c μ i : k) * (Sc.t i j : k)) •
          (plcL D Sc μ [] [up j] [] [] (bubRs cs i (wt D μ [up j]) (n - d : ℕ)) ≫
            cl D Sc μ [up j] [up j] (dotsL [] j [] q)) else 0) =
      ((cs.c μ i : k) * a) •
        (plcL D Sc μ [] [up j] [] [] (bubRs cs i (wt D μ [up j]) ((n : ℤ) - d)) ≫
          cl D Sc μ [up j] [up j] (dotsL [] j [] q)) := by
    by_cases h : d ≤ n
    · rw [ite_eq_left h, smul_smul, ht, Nat.cast_sub h]
    · rw [ite_eq_right h, smul_zero, bubRs_neg cs i _ (by omega), map_zero, Limits.zero_comp, smul_zero]
  simp only [mul_comm (Sc.t i j : k) (cs.c μ i : k)]
  rw [hterm]
  apply congrArg₂ (· + ·) rfl
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q _
  rw [hterm]
  have hp := mem_Ioo.mp hp
  congr 4
  omega

theorem isg_sub_nat_of_even (i : I) (n : ℤ) (d : ℕ)
    (hd : D.parity i * (d : ZMod 2) = 0) :
    isg k (D.parity i) (n - d) = isg k (D.parity i) n := by
  simp only [isg, Int.cast_sub, Int.cast_natCast, mul_sub, hd, sub_zero]

theorem bubbleL_conv_normalize (i j : I) (μ : X) (hd : 0 < D.dn i j) (n : ℕ) :
    bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
      (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) n =
    (isg k (D.parity i) n * (↑(cs.c (wt D μ [up j]) i)⁻¹ : k)) • bubbleSlideRHSL cs i j μ n := by
  rw [bubblePolynomialCoeff_conv_left i j μ hd]
  have hl (r : ℕ) : rbub j μ (bubbleCoeffL cs i (wt D μ []) r) =
      (isg k (D.parity i) r * (↑(cs.c μ i)⁻¹ : k)) • rbub j μ (bubLs cs i (wt D μ []) r) := by
    unfold bubbleCoeffL rbub
    erw [map_smul]
    rfl
  simp only [hl]
  simp only [bubbleSlideRHSL, rbub, Linear.comp_smul,
    smul_add, smul_sum, smul_smul, c_wt_upj, mul_inv, Units.val_mul]
  have hzero : isg k (D.parity i) n * ((↑(Sc.t i j)⁻¹ : k) * (↑(cs.c μ i)⁻¹ : k)) * (Sc.t i j : k) =
      isg k (D.parity i) n * (↑(cs.c μ i)⁻¹ : k) := by
    calc
      _ = ((↑(Sc.t i j)⁻¹ : k) * (Sc.t i j : k)) * (isg k (D.parity i) n * (↑(cs.c μ i)⁻¹ : k)) := by ring
      _ = _ := by rw [Units.inv_mul, one_mul]
  rw [hzero]
  have hterm (d q : ℕ) (a : k) (he : D.parity i * (d : ZMod 2) = 0) :
      ((↑(Sc.t i j)⁻¹ : k) * a) • (if d ≤ n then
        (isg k (D.parity i) (n - d : ℕ) * (↑(cs.c μ i)⁻¹ : k)) •
          (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
            plcL D Sc μ [up j] [] [] [] (bubLs cs i (wt D μ []) (n - d : ℕ))) else 0) =
      (isg k (D.parity i) n * ((↑(Sc.t i j)⁻¹ : k) * (↑(cs.c μ i)⁻¹ : k)) * a) •
        (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          plcL D Sc μ [up j] [] [] [] (bubLs cs i (wt D μ []) ((n : ℤ) - d))) := by
    by_cases h : d ≤ n
    · rw [ite_eq_left h, smul_smul, Nat.cast_sub h, isg_sub_nat_of_even i n d he]
      congr 1
      ring
    · rw [ite_eq_right h, smul_zero, bubLs_neg cs i (wt D μ []) (by omega), map_zero, Limits.comp_zero, smul_zero]
  rw [hterm (D.dn i j) (D.dn j i) (Sc.t j i : k) (parity_mul_dn D i j)]
  apply congrArg₂ (· + ·) rfl
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q _
  have hp := mem_Ioo.mp hp
  by_cases hs : Sc.s i j p q = 0
  · simp only [hs, mul_zero, zero_smul]
  · have he : D.parity i * ((D.dn i j - p : ℕ) : ZMod 2) = 0 := by
      rw [Nat.cast_sub (by omega), mul_sub, parity_mul_dn,
        show D.parity i * (p : ZMod 2) = 0 by simpa [mul_comm] using (Sc.parity_of_ne_zero hs).1,
        sub_zero]
    rw [hterm (D.dn i j - p) q (Sc.s i j p q) he]
    congr 4
    omega

/-- Both connected polynomial slide identities in normalized coefficients, at every weight. -/
theorem bubbleCoeff_connected (i j : I) (μ : X) (hij : i ≠ j) (hd : 0 < D.d i j) :
    ((fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
      bubbleConvolution (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
        (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)) ∧
    ((fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)) =
      bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
        (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n))) := by
  have hdn : 0 < D.dn i j := by have := D.dn_cast hij; omega
  by_cases hh : D.h i μ ≤ 0
  · have hR : (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
        bubbleConvolution (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
          (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ) := by
      funext n
      cases n with
      | zero =>
        simp only [bubbleConvolution, Nat.zero_add, sum_range_one, Nat.sub_self,
          bubbleSlidePolynomialCoeff, ite_true, bubbleCoeffR_zero, lbub, rbub, plcL_id]
        erw [Category.id_comp]
        rfl
      | succ n =>
        rw [bubbleR_conv_normalize cs i j μ hdn]
        unfold bubbleCoeffR rbub
        erw [map_smul]
        change (cs.c μ i : k) • rbub j μ (bubRs cs i (wt D μ []) (n + 1 : ℕ)) = _
        rw [bubbleR_polynomial_natural_shift cs i j μ hij (by omega) (n + 1 : ℕ) (by omega)]
    exact ⟨hR, (bubbleCoeff_polynomial_iff cs i j μ).mp hR⟩
  · by_cases hl : D.h i μ < D.d i j
    · exact bubbleCoeff_middle cs i j μ hij (by omega) hl
    · have hL : (fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)) =
          bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
            (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) := by
        funext n
        cases n with
        | zero =>
          simp only [bubbleConvolution, Nat.zero_add, sum_range_one, Nat.sub_self,
            bubbleSlidePolynomialCoeff, ite_true, bubbleCoeffL_zero, lbub, rbub, plcL_id]
          erw [Category.id_comp]
          rfl
        | succ n =>
          rw [bubbleL_conv_normalize cs i j μ hdn]
          unfold bubbleCoeffL lbub
          erw [map_smul]
          change (isg k (D.parity i) (n + 1 : ℕ) * (↑(cs.c (wt D μ [up j]) i)⁻¹ : k)) •
            lbub j μ (bubLs cs i (wt D μ [up j]) (n + 1 : ℕ)) = _
          rw [bubbleL_polynomial_natural_shift cs i j μ hij (by omega) (n + 1 : ℕ) (by omega)]
      exact ⟨(bubbleCoeff_polynomial_iff cs i j μ).mpr hL, hL⟩

/-- Brundan–Ellis Proposition 7.3(iii), (7.11), for every connected pair,
weight, and integer shifted degree. Fake bubbles are included. -/
theorem eq_7_11_connected (i j : I) (μ : X) (hij : i ≠ j) (hd : 0 < D.d i j) (n : ℤ) :
    rbub j μ (bubRs cs i (wt D μ []) n) =
    (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) n) +
    (Sc.t j i : k) • (lbub j μ (bubRs cs i (wt D μ [up j]) (n - D.dn i j)) ≫
      cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))) +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      Sc.s i j p q • (lbub j μ (bubRs cs i (wt D μ [up j]) (n + p - D.dn i j)) ≫
        cl D Sc μ [up j] [up j] (dotsL [] j [] q)) := by
  by_cases hn : n < 0
  · simp only [bubRs_neg cs i _ hn, bubRs_neg cs i _ (show n - D.dn i j < 0 by omega),
      rbub, lbub, map_zero, Limits.zero_comp, smul_zero, zero_add]
    symm
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro q _
    rw [bubRs_neg cs i _ (by have := mem_Ioo.mp hp; omega), map_zero, Limits.zero_comp, smul_zero]
  · change rbub j μ (bubRs cs i (wt D μ []) n) = bubbleSlideRHSR cs i j μ n
    have H := congrFun (bubbleCoeff_connected cs i j μ hij hd).1 n.toNat
    have hdn : 0 < D.dn i j := by have := D.dn_cast hij; omega
    rw [bubbleR_conv_normalize cs i j μ hdn] at H
    unfold bubbleCoeffR rbub at H
    erw [map_smul] at H
    have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    simp only [he, wt_nil] at H
    apply (cs.c μ i).isUnit.smul_left_cancel.mp
    exact H

/-- Brundan–Ellis Proposition 7.3(iii), (7.12), in the opposite orientation,
with the entire polynomial and all fake-bubble degrees. -/
theorem eq_7_12_connected (i j : I) (μ : X) (hij : i ≠ j) (hd : 0 < D.d i j) (n : ℤ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) =
    (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) +
    (Sc.t j i : k) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
      rbub j μ (bubLs cs i (wt D μ []) (n - D.dn i j))) +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      Sc.s i j p q • (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
        rbub j μ (bubLs cs i (wt D μ []) (n + p - D.dn i j))) := by
  by_cases hn : n < 0
  · simp only [bubLs_neg cs i _ hn, bubLs_neg cs i _ (show n - D.dn i j < 0 by omega),
      rbub, lbub, map_zero, Limits.comp_zero, smul_zero, zero_add]
    symm
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro q _
    rw [bubLs_neg cs i _ (by have := mem_Ioo.mp hp; omega), map_zero, Limits.comp_zero, smul_zero]
  · change lbub j μ (bubLs cs i (wt D μ [up j]) n) = bubbleSlideRHSL cs i j μ n
    have H := congrFun (bubbleCoeff_connected cs i j μ hij hd).2 n.toNat
    have hdn : 0 < D.dn i j := by have := D.dn_cast hij; omega
    rw [bubbleL_conv_normalize cs i j μ hdn] at H
    unfold bubbleCoeffL lbub at H
    erw [map_smul] at H
    have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    simp only [he] at H
    apply ((zsign_isUnit (k := k) (D.parity i * (n : ZMod 2))).mul
      ((cs.c (wt D μ [up j]) i)⁻¹).isUnit).smul_left_cancel.mp
    exact H

end OddMath.SKM

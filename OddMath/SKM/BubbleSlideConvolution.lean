/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideDotted
/-!
# Shifted middle-weight convolution

The arbitrary dotted contraction in the proof of Brundan–Ellis,
arXiv:1701.04133v2, Proposition 7.3(iii), combines with the natural-dot
polynomial slide to give the full ordered convolution recurrence.
The vanishing ends of the sum are removed before shifting; the factor
`isg k (D.parity i) (D.h i μ - 1)` is retained and then cancelled as a unit.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem bubbleL_right_dots_even (i j : I) (μ : X) (s : ℤ) (q : ℕ)
    (hq : (q : ZMod 2) * D.parity j = 0) :
    bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) =
    cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫ bubbleL_right cs i j μ s := by
  have H := plcL_right_interchange (Sc := Sc) μ [up j]
    (bubL_mem cs i (wt D μ []) s) (sChain_dotsL [] j [] q)
  simp only [map_whL_nil_nil, parsum_dotsL, hq, mul_zero, zsign_zero, one_smul] at H
  exact H

/-- A signed convolution, before shifting the dot count. -/
def bubbleSlideRawConv (i j : I) (μ : X) (q N : ℕ) :=
  ∑ s ∈ range N, zsign k (D.parity i * s) •
    (bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      bubbleR_left cs i j μ (N - 1 - s : ℕ))

theorem bubbleSlideRawConv_split (i j : I) (μ : X) (p q n : ℕ)
    (hp : D.parity i * (p : ZMod 2) = 0) :
    bubbleSlideRawConv cs i j μ q (p + n) =
    (∑ s ∈ range p, zsign k (D.parity i * s) •
      (bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
        bubbleR_left cs i j μ (p - 1 - s + n : ℕ))) +
    ∑ r ∈ range n, zsign k (D.parity i * r) •
      (bubbleL_right cs i j μ (r + p) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
        bubbleR_left cs i j μ (n - 1 - r : ℕ)) := by
  rw [bubbleSlideRawConv, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro r hr
    have he : p + n - 1 - r = p - 1 - r + n := by have := mem_range.mp hr; omega
    rw [he]
  · apply sum_congr rfl
    intro r _
    have he : p + n - 1 - (p + r) = n - 1 - r := by omega
    simp only [he, Nat.cast_add, mul_add, hp, zero_add]
    rw [add_comm (p : ℤ) r]

theorem bubble_slide_middle_raw_convolution (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (n : ℕ) :
    (Sc.t i j : k) • bubbleSlideRawConv cs i j μ 0 (D.dn i j + n) +
    (Sc.t j i : k) • bubbleSlideRawConv cs i j μ (D.dn j i) n +
    (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      Sc.s i j p q • bubbleSlideRawConv cs i j μ q (p + n)) = 0 := by
  have H := bubble_slide_middle_dotted_all cs i j μ hij hpos hlt n
  have hp := parity_mul_dn D i j
  rw [bubbleSlideRawConv_split cs i j μ (D.dn i j) 0 n hp]
  have hS : (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      Sc.s i j p q • bubbleSlideRawConv cs i j μ q (p + n)) =
      (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        Sc.s i j p q • ((∑ s ∈ range p, zsign k (D.parity i * s) •
          (bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
            bubbleR_left cs i j μ (p - 1 - s + n : ℕ))) +
        ∑ r ∈ range n, zsign k (D.parity i * r) •
          (bubbleL_right cs i j μ (r + p) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
            bubbleR_left cs i j μ (n - 1 - r : ℕ)))) := by
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases hs : Sc.s i j p q = 0
    · simp only [hs, zero_smul]
    · rw [bubbleSlideRawConv_split cs i j μ p q n (by simpa [mul_comm] using (Sc.parity_of_ne_zero hs).1)]
  rw [hS]
  simp only [smul_add, smul_sum, sum_add_distrib, smul_smul,
    dotsL, List.replicate_zero, cl_nil, Category.id_comp]
  have ht : (∑ r ∈ range n, (zsign k (D.parity i * r)) •
      (bubbleL_left cs i j μ r ≫ bubbleR_left cs i j μ (n - 1 - r : ℕ))) =
    (∑ r ∈ range n, ((Sc.t i j : k) * zsign k (D.parity i * r)) •
      (bubbleL_right cs i j μ (r + D.dn i j) ≫ bubbleR_left cs i j μ (n - 1 - r : ℕ))) +
    (Sc.t j i : k) • bubbleSlideRawConv cs i j μ (D.dn j i) n +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i), ∑ r ∈ range n,
      (Sc.s i j p q * zsign k (D.parity i * r)) •
        (bubbleL_right cs i j μ (r + p) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          bubbleR_left cs i j μ (n - 1 - r : ℕ)) := by
    simp only [bubbleL_slide_polynomial_raw cs i j μ hij (by omega),
      Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp,
      smul_add, smul_sum, smul_smul, sum_add_distrib, bubbleSlideRawConv]
    rw [sum_comm (s := range n) (t := Ioo 0 (D.dn i j))]
    simp_rw [sum_comm (s := range n) (t := Ioo 0 (D.dn j i))]
    apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · apply sum_congr rfl
        intro r _
        rw [mul_comm]
      · apply sum_congr rfl
        intro r _
        rw [← bubbleL_right_dots_even cs i j μ r (D.dn j i) (by simpa [mul_comm] using parity_mul_dn D j i)]
        simp only [Category.assoc, mul_comm]
    · apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro r _
      by_cases hs : Sc.s i j p q = 0
      · simp only [hs, mul_zero, zero_mul, zero_smul]
      · rw [← bubbleL_right_dots_even cs i j μ (r + p) q (Sc.parity_of_ne_zero hs).2]
        simp only [Category.assoc, mul_comm]
  rw [ht] at H
  rw [eq_neg_iff_add_eq_zero] at H
  simp only [mul_comm, dotsL] at H ⊢
  convert H using 1
  abel
theorem sum_range_shift_vanishing {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M)
    (a b m : ℕ) (ha : ∀ r s, r < a → f r s = 0)
    (hb : ∀ r s, s < b → f r s = 0) :
    (∑ r ∈ range (a + b + m + 1), f r (a + b + m - r)) =
      ∑ r ∈ range (m + 1), f (a + r) (b + m - r) := by
  have he : a + b + m + 1 = a + (m + 1 + b) := by omega
  rw [he, sum_range_add]
  have hzero : (∑ r ∈ range a, f r (a + b + m - r)) = 0 := by
    apply sum_eq_zero
    intro r hr
    exact ha _ _ (mem_range.mp hr)
  rw [hzero, zero_add, sum_range_add]
  have htail : (∑ r ∈ range b, f (a + (m + 1 + r)) (a + b + m - (a + (m + 1 + r)))) = 0 := by
    apply sum_eq_zero
    intro r hr
    exact hb _ _ (by have := mem_range.mp hr; omega)
  rw [htail, add_zero]
  apply sum_congr rfl
  intro r _
  congr 1
  omega

/-- The shifted ordered convolution between the two opposite-side natural families. -/
def bubbleSlideShiftConv (i j : I) (μ : X) (q m : ℕ) :=
  ∑ r ∈ range (m + 1), zsign k (D.parity i * r) •
    (rbub j μ (bubLs cs i (wt D μ []) r) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      lbub j μ (bubRs cs i (wt D μ [up j]) (m - r : ℕ)))

theorem bubbleSlideRawConv_shift (i j : I) (μ : X)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (q m : ℕ) :
    bubbleSlideRawConv cs i j μ q (D.dn i j - 1 + m) =
      isg k (D.parity i) (D.h i μ - 1) • bubbleSlideShiftConv cs i j μ q m := by
  let a := (D.h i μ - 1).toNat
  let b := (D.d i j - D.h i μ - 1).toNat
  have ha : (a : ℤ) = D.h i μ - 1 := Int.toNat_of_nonneg (by omega)
  have hb : (b : ℤ) = D.d i j - D.h i μ - 1 := Int.toNat_of_nonneg (by omega)
  have hd : (D.dn i j : ℤ) = D.d i j := Int.toNat_of_nonneg (by omega)
  have he : D.dn i j - 1 + m = a + b + m + 1 := by omega
  have he' : D.dn i j - 1 + m - 1 = a + b + m := by omega
  unfold bubbleSlideRawConv
  rw [he']
  rw [he]
  rw [sum_range_shift_vanishing (fun r s => zsign k (D.parity i * r) •
    (bubbleL_right cs i j μ r ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      bubbleR_left cs i j μ s)) a b m]
  · rw [bubbleSlideShiftConv, smul_sum]
    apply sum_congr rfl
    intro r hr
    have hrm : r ≤ m := by have := mem_range.mp hr; omega
    have hL : bubbleL_right cs i j μ (a + r : ℕ) = rbub j μ (bubLs cs i (wt D μ []) r) := by
      unfold bubbleL_right bubLs
      congr 2
      simp only [wt_nil, Nat.cast_add, ha]
      omega
    have hR : bubbleR_left cs i j μ (b + m - r : ℕ) =
        lbub j μ (bubRs cs i (wt D μ [up j]) (m - r : ℕ)) := by
      unfold bubbleR_left bubRs
      congr 2
      rw [h_wt_upj]
      omega
    rw [hL, hR, smul_smul]
    congr 1
    rw [Nat.cast_add, mul_add, zsign_add, isg_natCast, ha]
  · intro r s hr
    change zsign k _ • (rbub j μ (bubL cs i (wt D μ []) r) ≫ _ ≫ _) = 0
    rw [bubL_eq_zero_of_lt cs i _ (by rw [wt_nil]; omega), rbub, map_zero, Limits.zero_comp, smul_zero]
  · intro r s hs
    change zsign k _ • (_ ≫ _ ≫ lbub j μ (bubR cs i (wt D μ [up j]) s)) = 0
    rw [bubR_eq_zero_of_lt cs i _ (by rw [h_wt_upj]; omega), lbub, map_zero, Limits.comp_zero,
      Limits.comp_zero, smul_zero]

theorem bubbleSlideRawConv_below (i j : I) (μ : X)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (q N : ℕ)
    (hN : N < D.dn i j - 1) : bubbleSlideRawConv cs i j μ q N = 0 := by
  have hd : (D.dn i j : ℤ) = D.d i j := Int.toNat_of_nonneg (by omega)
  apply sum_eq_zero
  intro r hr
  have hrN := mem_range.mp hr
  by_cases hr : (r : ℤ) < D.h i μ - 1
  · change zsign k _ • (rbub j μ (bubL cs i (wt D μ []) r) ≫ _ ≫ _) = 0
    rw [bubL_eq_zero_of_lt cs i _ (by simpa using hr), rbub, map_zero, Limits.zero_comp, smul_zero]
  · change zsign k _ • (_ ≫ _ ≫ lbub j μ (bubR cs i (wt D μ [up j]) (N - 1 - r : ℕ))) = 0
    rw [bubR_eq_zero_of_lt cs i _ (by rw [h_wt_upj]; omega), lbub, map_zero,
      Limits.comp_zero, Limits.comp_zero, smul_zero]

theorem bubbleSlideRawConv_shift_all (i j : I) (μ : X)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (q N : ℕ) :
    bubbleSlideRawConv cs i j μ q N = isg k (D.parity i) (D.h i μ - 1) •
      (if D.dn i j - 1 ≤ N then bubbleSlideShiftConv cs i j μ q (N - (D.dn i j - 1)) else 0) := by
  split_ifs with hN
  · convert bubbleSlideRawConv_shift cs i j μ hpos hlt q (N - (D.dn i j - 1)) using 1
    congr 1
    omega
  · rw [bubbleSlideRawConv_below cs i j μ hpos hlt q N (by omega), smul_zero]

theorem bubble_slide_middle_shift_convolution (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (n : ℕ) :
    (Sc.t i j : k) • bubbleSlideShiftConv cs i j μ 0 (n + 1) +
    (Sc.t j i : k) • (if D.dn i j ≤ n + 1 then
      bubbleSlideShiftConv cs i j μ (D.dn j i) (n + 1 - D.dn i j) else 0) +
    (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      Sc.s i j p q • (if D.dn i j - p ≤ n + 1 then
        bubbleSlideShiftConv cs i j μ q (n + 1 - (D.dn i j - p)) else 0)) = 0 := by
  have H := bubble_slide_middle_raw_convolution cs i j μ hij hpos hlt n
  have hd : (D.dn i j : ℤ) = D.d i j := Int.toNat_of_nonneg (by omega)
  have he : D.dn i j + n = D.dn i j - 1 + (n + 1) := by omega
  rw [he, bubbleSlideRawConv_shift cs i j μ hpos hlt,
    bubbleSlideRawConv_shift_all cs i j μ hpos hlt (D.dn j i) n] at H
  have hz : (if D.dn i j - 1 ≤ n then bubbleSlideShiftConv cs i j μ (D.dn j i) (n - (D.dn i j - 1)) else 0) =
      (if D.dn i j ≤ n + 1 then bubbleSlideShiftConv cs i j μ (D.dn j i) (n + 1 - D.dn i j) else 0) := by
    have e : D.dn i j - 1 ≤ n ↔ D.dn i j ≤ n + 1 := by omega
    simp only [e]
    split_ifs
    · congr 1; omega
    · rfl
  rw [hz] at H
  have hs (p q : ℕ) (hp : p ∈ Ioo 0 (D.dn i j)) :
      bubbleSlideRawConv cs i j μ q (p + n) = isg k (D.parity i) (D.h i μ - 1) •
        (if D.dn i j - p ≤ n + 1 then bubbleSlideShiftConv cs i j μ q (n + 1 - (D.dn i j - p)) else 0) := by
    rw [bubbleSlideRawConv_shift_all cs i j μ hpos hlt]
    have hp := mem_Ioo.mp hp
    have e : D.dn i j - 1 ≤ p + n ↔ D.dn i j - p ≤ n + 1 := by omega
    simp only [e]
    congr 1
    split_ifs
    · congr 1; omega
    · rfl
  simp_rw [sum_congr rfl (fun p hp => sum_congr rfl (fun q _ =>
    congrArg (Sc.s i j p q • ·) (hs p q hp)))] at H
  apply ((zsign_isUnit (k := k) (D.parity i * ((D.h i μ - 1 : ℤ) : ZMod 2))).smul_eq_zero).mp
  change isg k (D.parity i) (D.h i μ - 1) • _ = 0
  simpa only [smul_add, smul_sum, smul_smul, mul_comm] using H

end OddMath.SKM

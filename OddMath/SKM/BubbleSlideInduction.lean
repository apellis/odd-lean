/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideConvolution
/-!
# Coefficient induction for connected middle-weight slides

The derived dotted recurrence, not a hypothesized series relation, supplies
the convolution coefficients. Strong coefficient induction and the actual
bubble inverses determine both orientations in all nonnegative shifted degrees.
This includes every missing fake-bubble degree for `0 < hᵢ(μ) < dᵢⱼ`.
Polynomial coefficients are commuted only after proving their dot parity from
the original scalar conditions. No restriction to even `i` is imposed.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w

private def seriesOne {C : Type*} [Category C] [Preadditive C] (Z : C) (n : ℕ) : Z ⟶ Z :=
  if n = 0 then 𝟙 Z else 0

private theorem conv_one_right {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A : ℕ → (Z ⟶ Z)) : bubbleConvolution A (seriesOne Z) = A := by
  funext n
  simp [bubbleConvolution, seriesOne, CategoryTheory.comp_ite]

private theorem conv_one_left {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A : ℕ → (Z ⟶ Z)) : bubbleConvolution (seriesOne Z) A = A := by
  funext n
  rw [bubbleConvolution, sum_eq_single n]
  · simp [seriesOne]
  · intro r hr hrn
    have he : n - r ≠ 0 := by have := mem_range.mp hr; omega
    simp [seriesOne, he]
  · simp

theorem bubbleConvolution_cancel_left {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B B' : ℕ → (Z ⟶ Z)) (hA : A 0 = 𝟙 Z)
    (h : bubbleConvolution A B = bubbleConvolution A B') : B = B' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have H := congrFun h n
    simp only [bubbleConvolution, sum_range_succ, Nat.sub_self, hA, Category.id_comp] at H
    have he : (∑ r ∈ range n, A (n - r) ≫ B r) = ∑ r ∈ range n, A (n - r) ≫ B' r := by
      apply sum_congr rfl
      intro r hr
      rw [ih r (mem_range.mp hr)]
    rw [he] at H
    exact add_left_cancel H

theorem bubbleCoeff_key_reverse {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B : ℕ → (Z ⟶ Z)) (hA : A 0 = 𝟙 Z) (hB : B 0 = 𝟙 Z)
    (hk : ∀ n, 0 < n → bubbleConvolution A B n = 0) (n : ℕ) (hn : 0 < n) :
    bubbleConvolution B A n = 0 := by
  have h : bubbleConvolution A B = seriesOne Z := by
    funext m
    cases m with
    | zero => simp [bubbleConvolution, seriesOne, hA, hB]
    | succ m => simpa [seriesOne] using hk (m + 1) (by omega)
  have H : bubbleConvolution B A = seriesOne Z := by
    apply bubbleConvolution_cancel_left A _ _ hA
    rw [← bubbleConvolution_assoc, h, conv_one_left, conv_one_right]
  rw [congrFun H n, seriesOne, ite_eq_right (by omega)]

/-- Delay a convolution term without extending any natural subtraction past its support. -/
theorem sum_range_conv_delay {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B : ℕ → (Z ⟶ Z)) (Q : Z ⟶ Z) (d m : ℕ) :
    (∑ r ∈ range (m + 1), A r ≫ (if d ≤ m - r then Q ≫ B (m - r - d) else 0)) =
    if d ≤ m then ∑ r ∈ range (m - d + 1), A r ≫ Q ≫ B (m - d - r) else 0 := by
  by_cases hd : d ≤ m
  · rw [ite_eq_left hd]
    symm
    calc
      _ = ∑ r ∈ range (m - d + 1), A r ≫ (if d ≤ m - r then Q ≫ B (m - r - d) else 0) := by
        apply sum_congr rfl
        intro r hr
        rw [ite_eq_left (by have := mem_range.mp hr; omega)]
        rw [show m - r - d = m - d - r by omega]
      _ = _ := sum_subset (range_mono (by omega)) (by
        intro r hr hnot
        simp only [mem_range] at hr hnot
        rw [ite_eq_right (by omega), Limits.comp_zero])
  · rw [ite_eq_right hd]
    apply sum_eq_zero
    intro r _
    rw [ite_eq_right (by omega), Limits.comp_zero]

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The same opposite-side convolution in normalized coefficients. -/
def bubbleSlideCoeffConv (i j : I) (μ : X) (q m : ℕ) :=
  ∑ r ∈ range (m + 1), rbub j μ (bubbleCoeffL cs i (wt D μ []) r) ≫
    cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) (m - r))

theorem bubbleSlideCoeffConv_eq (i j : I) (μ : X) (q m : ℕ) :
    bubbleSlideCoeffConv cs i j μ q m = (Sc.t i j : k) • bubbleSlideShiftConv cs i j μ q m := by
  rw [bubbleSlideCoeffConv, bubbleSlideShiftConv, smul_sum]
  apply sum_congr rfl
  intro r _
  simp only [bubbleCoeffL, bubbleCoeffR, rbub, lbub]
  erw [map_smul, map_smul]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, c_wt_upj, wt_nil, Units.val_mul]
  congr 1
  rw [isg_natCast]
  calc
    _ = (isg k (D.parity i) r * (Sc.t i j : k)) *
        ((↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k)) := by ring
    _ = _ := by rw [Units.inv_mul, mul_one]; ring

def bubbleSlideCandidateR (i j : I) (μ : X) (n : ℕ) :=
  (Sc.t i j : k) • lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n) +
  (Sc.t j i : k) • (if D.dn i j ≤ n then
    cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) (n - D.dn i j)) else 0) +
  ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
    Sc.s i j p q • (if D.dn i j - p ≤ n then
      cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
        lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) (n - (D.dn i j - p))) else 0)

theorem bubbleConvolution_eq_flip {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B : ℕ → (Z ⟶ Z)) (n : ℕ) :
    bubbleConvolution A B n = ∑ r ∈ range (n + 1), A r ≫ B (n - r) := by
  rw [bubbleConvolution, ← sum_range_reflect]
  apply sum_congr rfl
  intro r hr
  have he : n - (n - r) = r := by have := mem_range.mp hr; omega
  simp only [he, Nat.add_sub_cancel]

theorem bubbleSlideCandidateR_key (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (n : ℕ) :
    bubbleConvolution (fun r => rbub j μ (bubbleCoeffL cs i (wt D μ []) r))
      (bubbleSlideCandidateR cs i j μ) (n + 1) = 0 := by
  rw [bubbleConvolution_eq_flip]
  simp only [bubbleSlideCandidateR, Preadditive.comp_add, Linear.comp_smul,
    Preadditive.comp_sum, sum_add_distrib, ← smul_sum]
  rw [sum_comm (s := range (n + 1 + 1)) (t := Ioo 0 (D.dn i j))]
  simp_rw [sum_comm (s := range (n + 1 + 1)) (t := Ioo 0 (D.dn j i)), ← smul_sum]
  simp_rw [sum_range_conv_delay (fun r => rbub j μ (bubbleCoeffL cs i (wt D μ []) r))
    (fun r => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) r))]
  have hz : (∑ r ∈ range (n + 1 + 1), rbub j μ (bubbleCoeffL cs i (wt D μ []) r) ≫
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) (n + 1 - r))) =
      bubbleSlideCoeffConv cs i j μ 0 (n + 1) := by
    simp only [bubbleSlideCoeffConv, dotsL, List.replicate_zero, cl_nil, Category.id_comp]
  rw [hz]
  change (Sc.t i j : k) • bubbleSlideCoeffConv cs i j μ 0 (n + 1) +
    (Sc.t j i : k) • (if D.dn i j ≤ n + 1 then bubbleSlideCoeffConv cs i j μ (D.dn j i) (n + 1 - D.dn i j) else 0) +
    (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      Sc.s i j p q • (if D.dn i j - p ≤ n + 1 then bubbleSlideCoeffConv cs i j μ q (n + 1 - (D.dn i j - p)) else 0)) = 0
  simp_rw [bubbleSlideCoeffConv_eq]
  have H := congrArg ((Sc.t i j : k) • ·) (bubble_slide_middle_shift_convolution cs i j μ hij hpos hlt n)
  simp only [smul_add, smul_sum, smul_ite, smul_zero, smul_smul] at H ⊢
  simpa only [mul_comm] using H

/-- Coefficient induction through every missing degree, on the actual normalized bubbles. -/
theorem bubbleSlideCandidateR_middle (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) :
    bubbleSlideCandidateR cs i j μ = fun n => (Sc.t i j : k) •
      rbub j μ (bubbleCoeffR cs i (wt D μ []) n) := by
  have hR : (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) 0 = 𝟙 _ := by
    simp only [bubbleCoeffR_zero, rbub, plcL_id]; rfl
  have hL : (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) 0 = 𝟙 _ := by
    simp only [bubbleCoeffL_zero, rbub, plcL_id]; rfl
  apply bubble_conv_right_unique (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) _ _ hL
  · have hd : (D.dn i j : ℤ) = D.d i j := Int.toNat_of_nonneg (by omega)
    have hd0 : ¬ D.dn i j ≤ 0 := by omega
    simp only [bubbleSlideCandidateR, hd0, ite_false, smul_zero, add_zero, bubbleCoeffR_zero,
      lbub, rbub, plcL_id]
    have hz : (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        Sc.s i j p q • (if D.dn i j - p ≤ 0 then
          cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
            plcL D Sc μ [] [up j] [] [] (bubbleCoeffR cs i (wt D μ [up j]) (0 - (D.dn i j - p))) else 0)) = 0 := by
      apply sum_eq_zero
      intro p hp
      apply sum_eq_zero
      intro q _
      rw [ite_eq_right (by have := mem_Ioo.mp hp; omega), smul_zero]
    rw [hz, add_zero]
    rfl
  · intro n hn
    have he : n - 1 + 1 = n := by omega
    simpa only [he, bubbleConvolution] using bubbleSlideCandidateR_key cs i j μ hij hpos hlt (n - 1)
  · intro n hn
    have H := bubbleCoeff_key_reverse
      (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n))
      (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) hR hL
      (bubbleCoeff_key_place cs i μ [up j] []) n hn
    simpa only [bubbleConvolution, Linear.comp_smul, ← smul_sum, H, smul_zero] using
      congrArg ((Sc.t i j : k) • ·) H

def bubbleSlideMonomial (j : I) (μ : X) (d q : ℕ) (a : k) (n : ℕ) :=
  if n = d then a • cl D Sc μ [up j] [up j] (dotsL [] j [] q) else 0

theorem bubbleSlidePolynomialCoeff_add (i j : I) (μ : X) (hd : 0 < D.dn i j) (n : ℕ) :
    bubbleSlidePolynomialCoeff (Sc := Sc) i j μ n =
    (if n = 0 then 𝟙 _ else 0) +
    bubbleSlideMonomial j μ (D.dn i j) (D.dn j i) ((↑(Sc.t i j)⁻¹ : k) * (Sc.t j i : k)) n +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      bubbleSlideMonomial j μ (D.dn i j - p) q ((↑(Sc.t i j)⁻¹ : k) * Sc.s i j p q) n := by
  by_cases hn : n = 0
  · subst n
    simp only [bubbleSlidePolynomialCoeff, bubbleSlideMonomial, ite_true,
      ite_eq_right (show (0 : ℕ) ≠ D.dn i j by omega), add_zero]
    symm
    apply add_eq_left.mpr
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro q _
    rw [ite_eq_right (by have := mem_Ioo.mp hp; omega)]
  · simp only [bubbleSlidePolynomialCoeff, bubbleSlideMonomial, hn, ite_false, zero_add]

theorem bubbleSlideMonomial_sum (j : I) (μ : X) (d q n : ℕ) (a : k)
    (B : ℕ → ((pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j]))) :
    (∑ r ∈ range (n + 1), bubbleSlideMonomial (Sc := Sc) j μ d q a r ≫ B (n - r)) =
    a • (if d ≤ n then cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫ B (n - d) else 0) := by
  simp [bubbleSlideMonomial, ite_comp, Linear.smul_comp, mem_range, smul_ite]

theorem bubblePolynomialCoeff_conv_left (i j : I) (μ : X) (hd : 0 < D.dn i j) (n : ℕ)
    (B : ℕ → ((pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j]))) :
    bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ) B n =
    B n + ((↑(Sc.t i j)⁻¹ : k) * (Sc.t j i : k)) •
      (if D.dn i j ≤ n then cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫ B (n - D.dn i j) else 0) +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      ((↑(Sc.t i j)⁻¹ : k) * Sc.s i j p q) • (if D.dn i j - p ≤ n then
        cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫ B (n - (D.dn i j - p)) else 0) := by
  rw [bubbleConvolution_eq_flip]
  simp only [bubbleSlidePolynomialCoeff_add i j μ hd, Preadditive.add_comp, Preadditive.sum_comp, sum_add_distrib]
  rw [sum_comm (s := range (n + 1)) (t := Ioo 0 (D.dn i j))]
  simp_rw [sum_comm (s := range (n + 1)) (t := Ioo 0 (D.dn j i)), bubbleSlideMonomial_sum]
  simp [ite_comp]

/-- The actual middle-weight clockwise coefficient identity, with the factor order recorded. -/
theorem bubbleCoeffR_middle_left_polynomial (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) :
    (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
      bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
        (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n)) := by
  funext n
  apply (Sc.t i j).isUnit.smul_left_cancel.mp
  have H := congrFun (bubbleSlideCandidateR_middle cs i j μ hij hpos hlt) n
  have hd : 0 < D.dn i j := by
    have he : (D.dn i j : ℤ) = D.d i j := Int.toNat_of_nonneg (by omega)
    omega
  rw [bubblePolynomialCoeff_conv_left i j μ hd, smul_add, smul_add, smul_sum]
  simp only [smul_sum, smul_smul, ← mul_assoc, Units.mul_inv, one_mul]
  exact H.symm

theorem bubbleSlidePolynomialCoeff_comm (i j : I) (μ : X)
    (F : (pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j]))
    (hF : ∀ q : ℕ, (q : ZMod 2) * D.parity j = 0 →
      cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫ F =
        F ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q)) (n : ℕ) :
    bubbleSlidePolynomialCoeff (Sc := Sc) i j μ n ≫ F =
      F ≫ bubbleSlidePolynomialCoeff (Sc := Sc) i j μ n := by
  by_cases hn : n = 0
  · simp [bubbleSlidePolynomialCoeff, hn]
  · simp only [bubbleSlidePolynomialCoeff, hn, ite_false, Preadditive.add_comp,
      Preadditive.comp_add, Preadditive.sum_comp, Preadditive.comp_sum]
    apply congrArg₂ (· + ·)
    · split_ifs
      · rw [Linear.smul_comp, Linear.comp_smul,
          hF (D.dn j i) (by simpa [mul_comm] using parity_mul_dn D j i)]
      · simp
    · apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro q _
      split_ifs
      · by_cases hs : Sc.s i j p q = 0
        · simp [hs]
        · rw [Linear.smul_comp, Linear.comp_smul, hF q (Sc.parity_of_ne_zero hs).2]
      · simp

theorem bubbleCoeffR_left_polynomial_comm (i j : I) (μ : X) (r n : ℕ) :
    bubbleSlidePolynomialCoeff (Sc := Sc) i j μ n ≫
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) r) =
    lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) r) ≫
      bubbleSlidePolynomialCoeff (Sc := Sc) i j μ n := by
  apply bubbleSlidePolynomialCoeff_comm
  intro q hq
  have H := plcL_left_interchange (Sc := Sc) μ [up j]
    (bubbleCoeffR_mem cs i (wt D μ [up j]) r) (sChain_dotsL [] j [] q)
  simp only [map_whL_nil_nil, parsum_dotsL, hq, mul_zero, zsign_zero, one_smul] at H
  exact H.symm

/-- Both actual connected middle-weight coefficient identities, including every fake degree. -/
theorem bubbleCoeff_middle (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) :
    ((fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
      bubbleConvolution (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
        (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)) ∧
    ((fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)) =
      bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
        (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n))) := by
  have hr := bubbleCoeffR_middle_left_polynomial cs i j μ hij hpos hlt
  have he : bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
      (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n)) =
      bubbleConvolution (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
        (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ) := by
    funext n
    rw [bubbleConvolution_eq_flip]
    unfold bubbleConvolution
    apply sum_congr rfl
    intro r _
    exact bubbleCoeffR_left_polynomial_comm cs i j μ (n - r) r
  rw [he] at hr
  exact ⟨hr, (bubbleCoeff_polynomial_iff cs i j μ).mp hr⟩

end OddMath.SKM

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideRaw
import OddMath.SKM.BubbleSeries
/-!
# Scalar-corrected disconnected bubble slides

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 7.3(iv), (7.13)–(7.14). Both equations require a factor `tᵢⱼ`
on the right-hand side; see `ERRATA.md`.

The parameter `n` is the shifted degree from (2.17), not the actual dot count.
The actual counts are `n - h - 1` for `bubRs` and `n + h - 1` for `bubLs`.
When `dᵢⱼ = 0`, the coroot value `h` is the same on both sides of `Eⱼ`.
Natural-dot slides give one normalized family at each weight. Convolution
uniqueness then supplies the other, including the fake bubbles. No scalar is
specialized and no relation is added to the presentation.

Only part (iv) of Proposition 7.3 is proved here, not parts (i)–(iii).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- For disconnected colours the coroot value is unchanged across the strand. -/
theorem h_wt_upj_of_d_zero (i j : I) (μ : X) (hd : D.d i j = 0) :
    D.h i (wt D μ [up j]) = D.h i μ := by rw [h_wt_upj, hd, sub_zero]

theorem bubbleCoeffR_slide_iff (i j : I) (μ : X) (n : ℕ) :
    rbub j μ (bubbleCoeffR cs i (wt D μ []) n) =
        lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n) ↔
      rbub j μ (bubRs cs i (wt D μ []) n) =
        (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) n) := by
  simp only [bubbleCoeffR, rbub, lbub, map_smul, c_wt_upj, wt_nil, Units.val_mul]
  rw [show (Sc.t i j : k) * (cs.c μ i : k) = (cs.c μ i : k) * (Sc.t i j : k) by ring,
    ← smul_smul]
  exact (cs.c μ i).isUnit.smul_left_cancel

theorem bubbleCoeffL_slide_iff (i j : I) (μ : X) (n : ℕ) :
    lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n) =
        rbub j μ (bubbleCoeffL cs i (wt D μ []) n) ↔
      lbub j μ (bubLs cs i (wt D μ [up j]) n) =
        (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) := by
  simp only [bubbleCoeffL, rbub, lbub, map_smul]
  have ht : isg k (D.parity i) n * (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) * (Sc.t i j : k) =
      isg k (D.parity i) n * (↑(cs.c (wt D μ []) i)⁻¹ : k) := by
    simp only [c_wt_upj, mul_inv, Units.val_mul, wt_nil]
    calc
      _ = isg k (D.parity i) n * ((↑(Sc.t i j)⁻¹ : k) * (Sc.t i j : k)) *
        (↑(cs.c μ i)⁻¹ : k) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  conv_lhs => rhs; rw [← ht, mul_smul]
  have hu : IsUnit (isg k (D.parity i) n * (↑(cs.c (wt D μ [up j]) i)⁻¹ : k)) :=
    (zsign_isUnit _).mul (cs.c (wt D μ [up j]) i)⁻¹.isUnit
  exact hu.smul_left_cancel

theorem bubbleCoeffR_slide_nonpos (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0)
    (hh : D.h i μ ≤ 0) (n : ℕ) :
    rbub j μ (bubbleCoeffR cs i (wt D μ []) n) =
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [bubbleCoeffR_zero, rbub, lbub, plcL_id]; rfl
  apply (bubbleCoeffR_slide_iff cs i j μ n).mpr
  have H := bubbleR_slide_zero_raw cs i j μ hij hd ((n : ℤ) - D.h i μ - 1).toNat
  have hnat : (0 : ℤ) ≤ n - D.h i μ - 1 := by omega
  simpa only [bubbleR_right, bubbleR_left, bubRs, h_wt_upj_of_d_zero i j μ hd,
    wt_nil, Int.toNat_of_nonneg hnat] using H

theorem bubbleCoeffL_slide_nonneg (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0)
    (hh : 0 ≤ D.h i μ) (n : ℕ) :
    lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n) =
      rbub j μ (bubbleCoeffL cs i (wt D μ []) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [bubbleCoeffL_zero, rbub, lbub, plcL_id]; rfl
  apply (bubbleCoeffL_slide_iff cs i j μ n).mpr
  have H := bubbleL_slide_zero_raw cs i j μ hij hd ((n : ℤ) + D.h i μ - 1).toNat
  have hnat : (0 : ℤ) ≤ n + D.h i μ - 1 := by omega
  simpa only [bubbleL_right, bubbleL_left, bubLs, h_wt_upj_of_d_zero i j μ hd,
    wt_nil, Int.toNat_of_nonneg hnat] using H

/-- Both normalized coefficient families slide across a disconnected strand,
including all fake-bubble degrees. -/
theorem bubbleCoeff_slide (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0) :
    (∀ n, rbub j μ (bubbleCoeffR cs i (wt D μ []) n) =
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n)) ∧
    (∀ n, lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n) =
      rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) := by
  let Rr := fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)
  let Rl := fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n)
  let Lr := fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)
  let Ll := fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)
  have kr : ∀ n, 0 < n → ∑ r ∈ range (n + 1), Rr (n - r) ≫ Lr r = 0 :=
    bubbleCoeff_key_place cs i μ [up j] []
  have kl : ∀ n, 0 < n → ∑ r ∈ range (n + 1), Rl (n - r) ≫ Ll r = 0 :=
    bubbleCoeff_key_place cs i μ [] [up j]
  rcases le_total (D.h i μ) 0 with hh | hh
  · have hR : Rr = Rl := funext (bubbleCoeffR_slide_nonpos cs i j μ hij hd hh)
    have hL : Ll = Lr := by
      apply bubble_conv_right_unique Rl Ll Lr
      · simp only [Rl, lbub, bubbleCoeffR_zero, plcL_id]; rfl
      · simp only [Ll, Lr, lbub, rbub, bubbleCoeffL_zero, plcL_id]; rfl
      · exact kl
      · simpa only [← hR] using kr
    exact ⟨congrFun hR, congrFun hL⟩
  · have hL : Ll = Lr := funext (bubbleCoeffL_slide_nonneg cs i j μ hij hd hh)
    have hR : Rr = Rl := by
      apply bubble_conv_left_unique Rr Rl Lr
      · simp only [Lr, rbub, bubbleCoeffL_zero, plcL_id]; rfl
      · simp only [Rl, Rr, lbub, rbub, bubbleCoeffR_zero, plcL_id]; rfl
      · exact kr
      · simpa only [← hL] using kl
    exact ⟨congrFun hR, congrFun hL⟩

/-- Brundan–Ellis, Proposition 7.3(iv), (7.13), with the missing RHS factor `tᵢⱼ`.
No scalar specialization is made. -/
theorem eq_7_13_corrected (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0) (n : ℕ) :
    rbub j μ (bubRs cs i (wt D μ []) n) =
      (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) n) :=
  (bubbleCoeffR_slide_iff cs i j μ n).mp ((bubbleCoeff_slide cs i j μ hij hd).1 n)

/-- Brundan–Ellis, Proposition 7.3(iv), (7.14), with the missing RHS factor `tᵢⱼ`.
The bubble moves left-to-right, opposite to (7.13). -/
theorem eq_7_14_corrected (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0) (n : ℕ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) =
      (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) :=
  (bubbleCoeffL_slide_iff cs i j μ n).mp ((bubbleCoeff_slide cs i j μ hij hd).2 n)

end OddMath.SKM

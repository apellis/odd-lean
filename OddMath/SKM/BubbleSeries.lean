/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Placement
/-!
# Uniqueness of normalized bubble coefficients

The convolution identity `bubble_key` from the infinite Grassmannian relations
makes the two normalized bubble families determine each other. This also holds
after placing the bubbles alongside fixed words. It includes fake bubbles.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w

/-- Uniqueness of the right factor of a convolution inverse with constant coefficient one. -/
theorem bubble_conv_right_unique {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B B' : ℕ → (Z ⟶ Z)) (hA : A 0 = 𝟙 Z) (hB : B 0 = B' 0)
    (hAB : ∀ n, 0 < n → ∑ r ∈ range (n + 1), A (n - r) ≫ B r = 0)
    (hAB' : ∀ n, 0 < n → ∑ r ∈ range (n + 1), A (n - r) ≫ B' r = 0) : B = B' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn] using hB
    have hb := hAB n (by omega)
    have hb' := hAB' n (by omega)
    rw [sum_range_succ, Nat.sub_self, hA, Category.id_comp] at hb hb'
    have hs : ∑ r ∈ range n, A (n - r) ≫ B r = ∑ r ∈ range n, A (n - r) ≫ B' r := by
      apply sum_congr rfl
      intro r hr
      rw [ih r (mem_range.mp hr)]
    rw [hs] at hb
    exact add_left_cancel (hb.trans hb'.symm)

/-- Uniqueness of the left factor of a convolution inverse with constant coefficient one. -/
theorem bubble_conv_left_unique {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A A' B : ℕ → (Z ⟶ Z)) (hB : B 0 = 𝟙 Z) (hA : A 0 = A' 0)
    (hAB : ∀ n, 0 < n → ∑ r ∈ range (n + 1), A (n - r) ≫ B r = 0)
    (hAB' : ∀ n, 0 < n → ∑ r ∈ range (n + 1), A' (n - r) ≫ B r = 0) : A = A' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn] using hA
    have hb := hAB n (by omega)
    have hb' := hAB' n (by omega)
    rw [sum_range_succ', Nat.sub_zero, hB, Category.comp_id] at hb hb'
    have hs : ∑ r ∈ range n, A (n - (r + 1)) ≫ B (r + 1) =
        ∑ r ∈ range n, A' (n - (r + 1)) ≫ B (r + 1) := by
      apply sum_congr rfl
      intro r hr
      rw [ih (n - (r + 1)) (by omega)]
    rw [hs] at hb
    exact add_left_cancel (hb.trans hb'.symm)

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- Normalized clockwise coefficients. -/
def bubbleCoeffR (i : I) (μ : X) (n : ℕ) := (cs.c μ i : k) • bubRs cs i μ n
/-- Signed normalized counterclockwise coefficients. -/
def bubbleCoeffL (i : I) (μ : X) (n : ℕ) :=
  (isg k (D.parity i) n * (↑(cs.c μ i)⁻¹ : k)) • bubLs cs i μ n

theorem bubbleCoeffR_zero (i : I) (μ : X) : bubbleCoeffR cs i μ 0 = 𝟙 _ := by
  simp [bubbleCoeffR, bubRs_zero, smul_smul]
theorem bubbleCoeffL_zero (i : I) (μ : X) : bubbleCoeffL cs i μ 0 = 𝟙 _ := by
  simp [bubbleCoeffL, bubLs_zero, smul_smul, isg_zero]

theorem bubbleCoeffR_mem (i : I) (μ : X) (n : ℕ) :
    bubbleCoeffR cs i μ n ∈ homPar D Sc μ [] [] (D.parity i * (n : ZMod 2)) := by
  unfold bubbleCoeffR bubRs
  apply Submodule.smul_mem
  have h := bubR_mem cs i μ ((n : ℤ) - D.h i μ - 1)
  rw [closedPar_eq, show (n : ℤ) - D.h i μ - 1 + D.h i μ + 1 = n by ring] at h
  exact h

theorem bubbleCoeffL_mem (i : I) (μ : X) (n : ℕ) :
    bubbleCoeffL cs i μ n ∈ homPar D Sc μ [] [] (D.parity i * (n : ZMod 2)) := by
  unfold bubbleCoeffL bubLs
  apply Submodule.smul_mem
  have h := bubL_mem cs i μ ((n : ℤ) + D.h i μ - 1)
  rw [closedPar_eq] at h
  convert h using 2
  rw [show (n : ℤ) + D.h i μ - 1 + D.h i μ + 1 = n + 2 * D.h i μ by ring]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl]
  ring

theorem bubbleCoeff_key (i : I) (μ : X) (n : ℕ) (hn : 0 < n) :
    ∑ r ∈ range (n + 1), bubbleCoeffR cs i μ (n - r) ≫ bubbleCoeffL cs i μ r = 0 := by
  rw [← bubble_key cs i μ n hn]
  apply sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by simpa using (Nat.le_of_lt_succ (mem_range.mp hr))
  simp only [bubbleCoeffR, bubbleCoeffL, Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [mul_assoc, Units.inv_mul, mul_one]
  rw [Nat.cast_sub hrn]

/-- The convolution identity remains valid after placement alongside any fixed words. -/
theorem bubbleCoeff_key_place (i : I) (μ : X) (u v : List (Letter I)) (n : ℕ) (hn : 0 < n) :
    ∑ r ∈ range (n + 1),
      plcL D Sc μ u v [] [] (bubbleCoeffR cs i (wt D μ v) (n - r)) ≫
        plcL D Sc μ u v [] [] (bubbleCoeffL cs i (wt D μ v) r) = 0 := by
  have H := congrArg (plcL D Sc μ u v [] []) (bubbleCoeff_key cs i (wt D μ v) n hn)
  rw [map_sum, map_zero] at H
  convert H using 1
  apply sum_congr rfl
  intro r _
  rw [plcL_comp_of_mem μ u v (bubbleCoeffR_mem cs i _ _) (bubbleCoeffL_mem cs i _ _)]

end OddMath.SKM

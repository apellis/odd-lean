/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSeries
/-!
# Degree-one factors between inverse bubble series

Finite convolution identities transport a degree-one correction between opposite
bubble orientations, without assuming that the coefficients commute.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory Finset

/-- Insert a degree-one factor after each coefficient. -/
def bubbleStepR {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A : ℕ → (Z ⟶ Z)) (Q : Z ⟶ Z) : ℕ → (Z ⟶ Z)
  | 0 => A 0
  | n + 1 => A (n + 1) + A n ≫ Q

/-- Insert a degree-one factor before each coefficient. -/
def bubbleStepL {C : Type*} [Category C] [Preadditive C] {Z : C}
    (Q : Z ⟶ Z) (B : ℕ → (Z ⟶ Z)) : ℕ → (Z ⟶ Z)
  | 0 => B 0
  | n + 1 => B (n + 1) + Q ≫ B n

/-- Move a degree-one factor across the convolution brackets; no commutativity is used. -/
theorem bubbleStep_conv {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B : ℕ → (Z ⟶ Z)) (Q : Z ⟶ Z) (n : ℕ) :
    ∑ r ∈ range (n + 1), bubbleStepR A Q (n - r) ≫ B r =
      ∑ r ∈ range (n + 1), A (n - r) ≫ bubbleStepL Q B r := by
  cases n with
  | zero => simp [bubbleStepR, bubbleStepL]
  | succ n =>
    have hr : ∑ r ∈ range (n + 1 + 1), bubbleStepR A Q (n + 1 - r) ≫ B r =
        (∑ r ∈ range (n + 1 + 1), A (n + 1 - r) ≫ B r) +
          ∑ r ∈ range (n + 1), (A (n - r) ≫ Q) ≫ B r := by
      rw [sum_range_succ, sum_range_succ (f := fun r => A (n + 1 - r) ≫ B r)]
      simp only [Nat.sub_self, bubbleStepR.eq_1]
      have he : ∑ r ∈ range (n + 1), bubbleStepR A Q (n + 1 - r) ≫ B r =
          ∑ r ∈ range (n + 1), (A (n + 1 - r) ≫ B r + (A (n - r) ≫ Q) ≫ B r) := by
        apply sum_congr rfl
        intro r hr
        have h : n + 1 - r = (n - r) + 1 := by have := mem_range.mp hr; omega
        rw [h, bubbleStepR, Preadditive.add_comp]
      rw [he, sum_add_distrib]
      abel
    have hl : ∑ r ∈ range (n + 1 + 1), A (n + 1 - r) ≫ bubbleStepL Q B r =
        (∑ r ∈ range (n + 1 + 1), A (n + 1 - r) ≫ B r) +
          ∑ r ∈ range (n + 1), (A (n - r) ≫ Q) ≫ B r := by
      rw [sum_range_succ', sum_range_succ' (f := fun r => A (n + 1 - r) ≫ B r)]
      simp only [bubbleStepL, Preadditive.comp_add, ← Category.assoc, sum_add_distrib,
        Nat.add_sub_add_right]
      abel
    exact hr.trans hl.symm

/-- A degree-one relation between inverse pairs transfers to the other orientation. -/
theorem bubbleStep_inverse {C : Type*} [Category C] [Preadditive C] {Z : C}
    (Rr Rl Lr Ll : ℕ → (Z ⟶ Z)) (Q : Z ⟶ Z)
    (hRr : Rr 0 = 𝟙 Z) (hRl : Rl 0 = 𝟙 Z) (hLr : Lr 0 = 𝟙 Z) (hLl : Ll 0 = 𝟙 Z)
    (kr : ∀ n, 0 < n → ∑ r ∈ range (n + 1), Rr (n - r) ≫ Lr r = 0)
    (kl : ∀ n, 0 < n → ∑ r ∈ range (n + 1), Rl (n - r) ≫ Ll r = 0) :
    Rr = bubbleStepR Rl Q ↔ Ll = bubbleStepL Q Lr := by
  constructor
  · intro h
    apply bubble_conv_right_unique Rl Ll (bubbleStepL Q Lr) hRl
    · simp only [bubbleStepL, hLl, hLr]
    · exact kl
    · intro n hn
      rw [← bubbleStep_conv, ← h]
      exact kr n hn
  · intro h
    apply bubble_conv_left_unique Rr (bubbleStepR Rl Q) Lr hLr
    · simp only [bubbleStepR, hRr, hRl]
    · exact kr
    · intro n hn
      rw [bubbleStep_conv, ← h]
      exact kl n hn
end OddMath.SKM

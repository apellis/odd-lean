/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSeries
import Mathlib.Algebra.BigOperators.Intervals
/-!
# Polynomial and series factors between inverse bubble series

Finite convolution identities transport arbitrary corrections between opposite
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

/-- Ordered convolution of endomorphism-valued coefficient families. -/
def bubbleConvolution {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A B : ℕ → (Z ⟶ Z)) (n : ℕ) : Z ⟶ Z :=
  ∑ r ∈ range (n + 1), A (n - r) ≫ B r

/-- Moving an arbitrary coefficient series across convolution brackets, without commutation. -/
theorem bubbleConvolution_assoc {C : Type*} [Category C] [Preadditive C] {Z : C}
    (A Q B : ℕ → (Z ⟶ Z)) :
    bubbleConvolution (bubbleConvolution A Q) B =
      bubbleConvolution A (bubbleConvolution Q B) := by
  funext n
  unfold bubbleConvolution
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have H := sum_range_diag_flip (n + 1)
    (fun r s => A (n - (r + s)) ≫ Q s ≫ B r)
  calc
    _ = ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1 - r), A (n - (r + s)) ≫ Q s ≫ B r := by
      apply sum_congr rfl
      intro r hr
      have he : n - r + 1 = n + 1 - r := by have := mem_range.mp hr; omega
      rw [he]
      apply sum_congr rfl
      intro s _
      rw [Nat.sub_sub]
    _ = ∑ t ∈ range (n + 1), ∑ r ∈ range (t + 1), A (n - (r + (t - r))) ≫ Q (t - r) ≫ B r := H.symm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro r hr
      have he : r + (t - r) = t := by have := mem_range.mp hr; omega
      rw [he]

/-- Any normalized polynomial or series correction transports to the opposite inverse pair.
No coefficient is assumed central and no factor order is reversed. -/
theorem bubbleConvolution_inverse {C : Type*} [Category C] [Preadditive C] {Z : C}
    (Rr Rl Lr Ll Q : ℕ → (Z ⟶ Z))
    (hRr : Rr 0 = 𝟙 Z) (hRl : Rl 0 = 𝟙 Z) (hLr : Lr 0 = 𝟙 Z) (hLl : Ll 0 = 𝟙 Z)
    (hQ : Q 0 = 𝟙 Z)
    (kr : ∀ n, 0 < n → bubbleConvolution Rr Lr n = 0)
    (kl : ∀ n, 0 < n → bubbleConvolution Rl Ll n = 0) :
    Rr = bubbleConvolution Rl Q ↔ Ll = bubbleConvolution Q Lr := by
  constructor
  · intro h
    apply bubble_conv_right_unique Rl Ll (bubbleConvolution Q Lr) hRl
    · simp [bubbleConvolution, hLl, hLr, hQ]
    · exact kl
    · intro n hn
      change bubbleConvolution Rl (bubbleConvolution Q Lr) n = 0
      rw [← bubbleConvolution_assoc, ← h]
      exact kr n hn
  · intro h
    apply bubble_conv_left_unique Rr (bubbleConvolution Rl Q) Lr hLr
    · simp [bubbleConvolution, hRr, hRl, hQ]
    · exact kr
    · intro n hn
      change bubbleConvolution (bubbleConvolution Rl Q) Lr n = 0
      rw [bubbleConvolution_assoc, ← h]
      exact kl n hn
end OddMath.SKM

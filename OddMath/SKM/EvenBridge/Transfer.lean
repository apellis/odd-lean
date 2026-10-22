/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Form
import OddMath.CoveringQuantum.UDot.MixedAdjointCoefficients
import OddMath.CoveringQuantum.UDot.MixedUpAdjointCoefficients
import OddMath.SKM.MatchingEndpointSupport

/-!
# Moving a letter across the form on `U̇`

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 10.1 (5):
the generators `E_i 1_ν`, `F_i 1_ν` have adjoints `q^{-dᵢ(1+⟨hᵢ,ν⟩)} F_i`, resp.
`q^{dᵢ(⟨hᵢ,ν⟩-1)} π^{|i,ν|} E_i`. For an even colour, on the mixed words
`G(a, b) = (E_a 1_μ, E_b 1_μ)` (`wordForm`) this reads

* `G((+i) a, b) = q^{dᵢ(1 - ⟨hᵢ, μ + |b|⟩)} G(a, (-i) b)` (`wordForm_cons_E`),
* `G((-i) a, b) = q^{dᵢ(1 + ⟨hᵢ, μ + |b|⟩)} G(a, (+i) b)` (`wordForm_cons_F`),

for all `a, b`, where `μ + |b|` is the left weight of `E_b 1_μ`: when the endpoints do not match,
both sides vanish. This is the transfer rule `B_rhoE` of the KL III form (Prop. 2.2 (iii)).
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open OddMath.CoveringQuantum OddMath.CoveringQuantum.UDot
  OddMath.CoveringQuantum.UDot.GenericTensor OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : CoveringQuantum.RootDatum I X)

/-- The form on mixed words `G(a, b) = (E_a 1_μ, E_b 1_μ)`. -/
abbrev wordForm (μ : X) (a b : List (Bool × I)) : Coefficients.Ring :=
  sesquilinearForm D (algebraWord D μ a) (algebraWord D μ b)

theorem h_α_self (i : I) : D.h i (D.α i) = 2 := by
  rw [D.h_α]; exact D.isGCM.diag i

theorem wordForm_cons_E (μ : X) (i : I) (a b : List (Bool × I)) :
    wordForm D μ ((true, i) :: a) b =
      qp Coefficients.q (D.d i * (1 - D.h i (μ + shift D b))) *
        wordForm D μ a ((false, i) :: b) := by
  by_cases hw : μ + shift D b = μ + shift D a + D.α i
  · have h := sesquilinearForm_E_adjoint D i (μ + shift D a)
      (algebraWord D μ a) (algebraWord D μ b)
    have hc : -(D.d i * (1 + D.h i (μ + shift D a))) =
        D.d i * (1 - D.h i (μ + shift D b)) := by
      rw [hw, map_add, h_α_self]; ring
    rw [hc, ← hw] at h
    simpa only [wordForm, algebraWord, halfGen, ite_true, Bool.false_eq_true, ite_false]
      using h
  · obtain ⟨h1, h2⟩ := sesquilinearForm_mixed_up_leftCons_mismatch D μ i a b (by
      rwa [mixed_word_physical_weight, mixed_word_physical_weight])
    rw [wordForm, h1, wordForm, h2, mul_zero]

theorem wordForm_cons_F (μ : X) (i : I) (hi : D.parity i = 0) (a b : List (Bool × I)) :
    wordForm D μ ((false, i) :: a) b =
      qp Coefficients.q (D.d i * (1 + D.h i (μ + shift D b))) *
        wordForm D μ a ((true, i) :: b) := by
  by_cases hw : μ + shift D b = μ + shift D a - D.α i
  · have h := sesquilinearForm_F_adjoint D i (μ + shift D a)
      (algebraWord D μ a) (algebraWord D μ b)
    have hc : D.d i * (D.h i (μ + shift D a) - 1) = D.d i * (1 + D.h i (μ + shift D b)) := by
      rw [hw, map_sub, h_α_self]; ring
    have hp : D.parl i (μ + shift D a) = 0 := by simp [CoveringQuantum.RootDatum.parl, hi]
    rw [hc, hp, ← hw] at h
    simpa only [wordForm, algebraWord, halfGen, ite_true, Bool.false_eq_true, ite_false,
      ZMod.val_zero, pow_zero, mul_one] using h
  · obtain ⟨h1, h2⟩ := sesquilinearForm_mixed_down_leftCons_mismatch D μ i a b (by
      rwa [mixed_word_physical_weight, mixed_word_physical_weight])
    rw [wordForm, h1, wordForm, h2, mul_zero]

end OddMath.SKM.EvenBridge

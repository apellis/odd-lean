/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairSector
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Division-free polynomial norm centrality in an ordinary ring.
Used for the reverse probe-pair Q product. -/

namespace QWeightedDraft

variable {R : Type*} [Ring R]

/-- The final cancellation, in its smallest usable form. -/
theorem norm_of_two_slides (ψ A B E : R)
    (hAB : A * B = B * A) (hBE : B * E = E * B)
    (hA : ψ * A = B * ψ + E) (hB : ψ * B = A * ψ - E) :
    ψ * (A * B) = (A * B) * ψ := by
  calc
    ψ * (A * B) = (B * ψ + E) * B := by rw [← mul_assoc, hA]
    _ = B * (ψ * B) + E * B := by noncomm_ring
    _ = B * (A * ψ - E) + E * B := by rw [hB]
    _ = (B * A) * ψ - B * E + E * B := by noncomm_ring
    _ = (A * B) * ψ := by rw [← hAB, hBE]; noncomm_ring

section Polynomial

variable {K S : Type*} [CommRing K] [CommRing S]
variable (c : K →+* S) (φ : S →+* R)
variable (ψ : R) (a b d : S)

/-- A strengthened slide tracks the division-free difference identity. -/
def SlidePair (A B : S) : Prop :=
  ∃ E : S,
    (a - b) * E = d * (A - B) ∧
    ψ * φ A = φ B * ψ + φ E ∧
    ψ * φ B = φ A * ψ - φ E

private theorem image_comm (x y : S) : φ x * φ y = φ y * φ x := by
  rw [← map_mul, ← map_mul, mul_comm x y]

/-- Polynomial values have equal and opposite correction terms.
The additional difference identity is preserved without cancelling a-b or d. -/
theorem polynomial_slides
    (hc : ∀ r : K, ψ * φ (c r) = φ (c r) * ψ)
    (ha : ψ * φ a = φ b * ψ + φ d)
    (hb : ψ * φ b = φ a * ψ - φ d)
    (F : Polynomial K) :
    SlidePair φ ψ a b d (F.eval₂ c a) (F.eval₂ c b) := by
  have step (A B : S) (h : SlidePair φ ψ a b d A B) :
      SlidePair φ ψ a b d (A * a) (B * b) := by
    obtain ⟨E, hd, hA, hB⟩ := h
    have he : B * d + E * a = A * d + E * b := by
      linear_combination hd
    refine ⟨B * d + E * a, ?_, ?_, ?_⟩
    · linear_combination a * hd
    · calc
        ψ * φ (A * a) = (φ B * ψ + φ E) * φ a := by
          rw [map_mul, ← mul_assoc, hA]
        _ = φ B * (ψ * φ a) + φ E * φ a := by noncomm_ring
        _ = φ B * (φ b * ψ + φ d) + φ E * φ a := by rw [ha]
        _ = φ (B * b) * ψ + φ (B * d + E * a) := by
          simp only [map_mul, map_add]
          noncomm_ring
    · calc
        ψ * φ (B * b) = (φ A * ψ - φ E) * φ b := by
          rw [map_mul, ← mul_assoc, hB]
        _ = φ A * (ψ * φ b) - φ E * φ b := by noncomm_ring
        _ = φ A * (φ a * ψ - φ d) - φ E * φ b := by rw [hb]
        _ = φ (A * a) * ψ - φ (A * d + E * b) := by
          simp only [map_mul, map_add]
          noncomm_ring
        _ = φ (A * a) * ψ - φ (B * d + E * a) := by rw [he]
  induction F using Polynomial.induction_on with
  | C r =>
      refine ⟨0, ?_, ?_, ?_⟩
      · simp
      · simpa using hc r
      · simpa using hc r
  | add F G hF hG =>
      obtain ⟨E, hE, hFA, hFB⟩ := hF
      obtain ⟨H, hH, hGA, hGB⟩ := hG
      refine ⟨E + H, ?_, ?_, ?_⟩
      · simp only [Polynomial.eval₂_add]
        linear_combination hE + hH
      · simp only [Polynomial.eval₂_add, map_add, mul_add, add_mul]
        rw [hFA, hGA]
        abel
      · simp only [Polynomial.eval₂_add, map_add, mul_add, add_mul]
        rw [hFB, hGB]
        noncomm_ring
  | monomial n r ih =>
      have hs := step _ _ ih
      simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_succ, mul_assoc] using hs

/-- Centrality of the norm of an arbitrary coefficient polynomial. -/
theorem polynomial_norm
    (hc : ∀ r : K, ψ * φ (c r) = φ (c r) * ψ)
    (ha : ψ * φ a = φ b * ψ + φ d)
    (hb : ψ * φ b = φ a * ψ - φ d)
    (F : Polynomial K) :
    ψ * (φ (F.eval₂ c a) * φ (F.eval₂ c b)) =
      (φ (F.eval₂ c a) * φ (F.eval₂ c b)) * ψ := by
  obtain ⟨E, _, hA, hB⟩ := polynomial_slides c φ ψ a b d hc ha hb F
  exact norm_of_two_slides _ _ _ _ (image_comm φ _ _) (image_comm φ _ _) hA hB

end Polynomial

/-- Odd slides become an ordinary swapped pair on squares, with correction x-z. -/
theorem odd_square_slides (ψ x z : R)
    (hx : ψ * x + z * ψ = 1) (hz : x * ψ + ψ * z = 1) :
    ψ * (x * x) = (z * z) * ψ + (x - z) ∧
    ψ * (z * z) = (x * x) * ψ - (x - z) := by
  have hx' : ψ * x = 1 - z * ψ := by
    rw [← hx]; noncomm_ring
  have hz' : ψ * z = 1 - x * ψ := by
    rw [← hz]; noncomm_ring
  constructor
  · calc
      ψ * (x * x) = (1 - z * ψ) * x := by rw [← mul_assoc, hx']
      _ = x - z * (ψ * x) := by noncomm_ring
      _ = (z * z) * ψ + (x - z) := by rw [hx']; noncomm_ring
  · calc
      ψ * (z * z) = (1 - x * ψ) * z := by rw [← mul_assoc, hz']
      _ = z - x * (ψ * z) := by noncomm_ring
      _ = (x * x) * ψ - (x - z) := by rw [hz']; noncomm_ring

end QWeightedDraft


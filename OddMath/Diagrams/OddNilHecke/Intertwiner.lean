/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Diagrams.OddNilHecke.Relations
import Mathlib.Tactic.NoncommRing

/-!
# The odd equal-colour intertwiner

Kang–Kashiwara–Oh, *Supercategorification of quantum Kac-Moody algebras*,
arXiv:1206.5933v2, (8.10) and Lemma 8.3: the equal-odd-colour intertwiner variant
`g = Δ (y - x) - Δ² τ`, with `Δ = y² - x²`, transports the two dots with
minus signs. The local relations also give its square `-Δ² (x² + y²)`.

The local identities hold in any ring satisfying the four two-strand odd
nilHecke relations. They are applied below to the existing presented
odd nilHecke category at every admissible position. The square identity
supplies the polynomial norm used in cyclotomic intertwiner cancellation;
no cyclotomic freeness, categorical action, or nondegeneracy follows here.
-/

noncomputable section

namespace OddMath.OddNilHecke.Intertwiner

variable {A : Type*} [Ring A]

/-- The difference of the squared dots. -/
def squareDiff (x y : A) : A := y ^ 2 - x ^ 2

/-- KKO's intertwiner in the equal odd-colour case. -/
def element (x y τ : A) : A :=
  squareDiff x y * (y - x) - squareDiff x y ^ 2 * τ

/-- Local transport, polynomial norm, and the signed reversed expression.
No invertibility of the dot difference is assumed. -/
theorem identities (x y τ : A)
    (hsquare : τ * τ = 0) (hdots : x * y + y * x = 0)
    (hleft : τ * x + y * τ = 1) (hright : x * τ + τ * y = 1) :
    element x y τ ^ 2 = -(squareDiff x y ^ 2 * (x ^ 2 + y ^ 2)) ∧
    element x y τ * x = -(y * element x y τ) ∧
    element x y τ * y = -(x * element x y τ) ∧
    element x y τ = -((τ * squareDiff x y - (y - x)) * squareDiff x y) ∧
    τ * element x y τ = τ * (y - x) * squareDiff x y := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right hdots
  have hτx : τ * x = 1 - y * τ := eq_sub_of_add_eq hleft
  have hτy : τ * y = 1 - x * τ := eq_sub_of_add_eq' hright
  have hyxa (a : A) : y * (x * a) = -(x * (y * a)) := by
    rw [← mul_assoc, hyx, neg_mul, mul_assoc]
  have hτxa (a : A) : τ * (x * a) = a - y * (τ * a) := by
    rw [← mul_assoc, hτx, sub_mul, one_mul, mul_assoc]
  have hτya (a : A) : τ * (y * a) = a - x * (τ * a) := by
    rw [← mul_assoc, hτy, sub_mul, one_mul, mul_assoc]
  have hττa (a : A) : τ * (τ * a) = 0 := by
    rw [← mul_assoc, hsquare, zero_mul]
  unfold element squareDiff
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hyx, hτx, hτy, hsquare, hyxa, hτxa, hτya, hττa]

/-- The intertwiner remains odd with respect to an independent odd coefficient.
No square-zero or relation between different coefficients is needed. -/
theorem anticommutes (x y τ d : A)
    (hx : d * x = -(x * d)) (hy : d * y = -(y * d))
    (hτ : d * τ = -(τ * d)) :
    d * element x y τ = -(element x y τ * d) := by
  have hxa (a : A) : d * (x * a) = -(x * (d * a)) := by
    rw [← mul_assoc, hx, neg_mul, mul_assoc]
  have hya (a : A) : d * (y * a) = -(y * (d * a)) := by
    rw [← mul_assoc, hy, neg_mul, mul_assoc]
  have hτa (a : A) : d * (τ * a) = -(τ * (d * a)) := by
    rw [← mul_assoc, hτ, neg_mul, mul_assoc]
  unfold element squareDiff
  noncomm_ring [hx, hy, hτ, hxa, hya, hτa]

end OddMath.OddNilHecke.Intertwiner

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory

variable (R : Type*) [CommRing R]

/-- The equal-odd-colour intertwiner at position `i`. -/
def intertwiner (n i : ℕ) : End ((pres R).obj (strands n)) :=
  OddMath.OddNilHecke.Intertwiner.element (x R n i) (x R n (i + 1)) (ψ R n i)

/-- KKO's polynomial norm at every admissible position in the presented category. -/
theorem intertwiner_square {n i : ℕ} (h : i + 1 < n) :
    intertwiner R n i ^ 2 =
      -((x R n (i + 1) ^ 2 - x R n i ^ 2) ^ 2 *
        (x R n i ^ 2 + x R n (i + 1) ^ 2)) := by
  exact (OddMath.OddNilHecke.Intertwiner.identities _ _ _ (ψ_mul_ψ R n i)
    (x_mul_x_add_x_mul_x R (by omega)) (ψ_mul_x_add_x_mul_ψ R h)
    (x_mul_ψ_add_ψ_mul_x R h)).1

/-- An intertwiner moves either dot to the opposite position with a minus sign. -/
theorem intertwiner_dot_transport {n i : ℕ} (h : i + 1 < n) :
    intertwiner R n i * x R n i = -(x R n (i + 1) * intertwiner R n i) ∧
    intertwiner R n i * x R n (i + 1) = -(x R n i * intertwiner R n i) := by
  have key := OddMath.OddNilHecke.Intertwiner.identities _ _ _ (ψ_mul_ψ R n i)
    (x_mul_x_add_x_mul_x R (by omega)) (ψ_mul_x_add_x_mul_ψ R h)
    (x_mul_ψ_add_ψ_mul_x R h)
  exact ⟨key.2.1, key.2.2.1⟩

end OddMath.Diagrams.OddNilHecke

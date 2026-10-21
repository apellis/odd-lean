import OddMath.Diagrams.EvenNilHecke.PolynomialAction

/-!
# Even nilHecke rings in ranks zero and one

The empty-word and one-strand cases of the divided-power idempotents before
BE2, arXiv:1701.04133v2, Lemma 11.1. They are the coefficient ring and the
one-variable polynomial ring, respectively, with projector one. Higher
ranks use the integral presentation, not the image of its polynomial action.
-/

namespace OddMath.EvenNilHecke

/-- Integral nilHecke rings indexed by the actual number of strands. -/
def RingAll : ℕ → Type
  | 0 => ℤ
  | 1 => MvPolynomial (Fin 1) ℤ
  | n + 2 => Presented n

noncomputable instance ringAllRing : (r : ℕ) → Ring (RingAll r)
  | 0 => inferInstanceAs (Ring ℤ)
  | 1 => inferInstanceAs (Ring (MvPolynomial (Fin 1) ℤ))
  | n + 2 => inferInstanceAs (Ring (Presented n))

instance ringAllNontrivial : (r : ℕ) → Nontrivial (RingAll r)
  | 0 => inferInstanceAs (Nontrivial ℤ)
  | 1 => inferInstanceAs (Nontrivial (MvPolynomial (Fin 1) ℤ))
  | n + 2 => inferInstanceAs (Nontrivial (Presented n))

/-- The empty product in ranks zero and one, and the longest product thereafter. -/
noncomputable def projectorAll : (r : ℕ) → RingAll r
  | 0 => 1
  | 1 => 1
  | n + 2 => projector n

theorem projectorAll_idempotent : (r : ℕ) →
    projectorAll r * projectorAll r = projectorAll r
  | 0 => one_mul _
  | 1 => one_mul _
  | n + 2 => projector_idempotent n

theorem projectorAll_ne_zero : (r : ℕ) → projectorAll r ≠ 0
  | 0 => one_ne_zero
  | 1 => one_ne_zero
  | n + 2 => projector_ne_zero n

#print axioms projectorAll_idempotent
#print axioms projectorAll_ne_zero

end OddMath.EvenNilHecke

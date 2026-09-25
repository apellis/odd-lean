import OddMath.Diagrammatics.Even.Basic

/-!
# Strand cancellation for the even permutation calculus

First even rewrite (section 4 of the unpublished design notes): equal adjacent permutation
crossings cancel. This is the symmetric-group involution `sᵢ² = 1` and must
not be confused with the odd nilHecke rules `dᵢ² = 0` (R-2.07A / R-3.05):
no nilHecke crossing identification is used anywhere in this module.
-/
namespace OddMath.Diagrammatics.Even

/-- Doubling an adjacent swap denotes the identity permutation. -/
theorem cancel_adjacent (k : Nat) (i : Fin (k + 1)) :
    denote (Expr.seq (Expr.swap k i) (Expr.swap k i)) = denote (Expr.id (k + 2)) := by
  simp only [denote, adjacent]
  exact Equiv.swap_swap _ _

/-- Cancellation inside a right context: `sᵢ sᵢ p = p`. -/
theorem cancel_left (k : Nat) (i : Fin (k + 1)) {a : Nat} (post : Expr (k + 2) a) :
    denote (Expr.seq (Expr.swap k i) (Expr.seq (Expr.swap k i) post)) =
      denote post := by
  have h := cancel_adjacent k i
  simp only [denote] at h ⊢
  rw [← Equiv.trans_assoc, h, Equiv.refl_trans]

/-- Cancellation inside a left context: `p sᵢ sᵢ = p`. -/
theorem cancel_right (k : Nat) {a : Nat} (pre : Expr a (k + 2)) (i : Fin (k + 1)) :
    denote (Expr.seq pre (Expr.seq (Expr.swap k i) (Expr.swap k i))) =
      denote pre := by
  have h := cancel_adjacent k i
  simp only [denote] at h ⊢
  rw [h, Equiv.trans_refl]

end OddMath.Diagrammatics.Even

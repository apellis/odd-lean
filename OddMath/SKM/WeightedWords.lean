import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Locally finite positive weighted words

The coefficient-word finiteness used in Brundan–Ellis, arXiv:1701.04133v2,
§§11–12. No commutativity or independence of the words is needed.
-/

namespace OddMath.SKM

/-- Positive locally finite letters have only finitely many words of bounded weight. -/
theorem finite_weighted_words {α : Type*} (w : α → ℕ) (hw : ∀ a, 0 < w a)
    (hf : ∀ N, Set.Finite {a | w a ≤ N}) (N : ℕ) :
    Set.Finite {l : List α | (l.map w).sum ≤ N} := by
  induction N with
  | zero =>
    apply (Set.finite_singleton []).subset
    intro l hl
    cases l with
    | nil => exact Set.mem_singleton _
    | cons a l =>
      simp only [List.map_cons, List.sum_cons, Set.mem_ofPred_eq] at hl
      have := hw a
      omega
  | succ N ih =>
    apply ((Set.finite_singleton []).union
      (((hf (N + 1)).prod ih).image (fun p : α × List α => p.1 :: p.2))).subset
    intro l hl
    cases l with
    | nil => exact Or.inl (Set.mem_singleton _)
    | cons a l =>
      simp only [List.map_cons, List.sum_cons, Set.mem_ofPred_eq] at hl
      apply Or.inr
      refine ⟨(a, l), ⟨?_, ?_⟩, rfl⟩
      · change w a ≤ N + 1
        omega
      · change (l.map w).sum ≤ N
        have := hw a
        omega

end OddMath.SKM

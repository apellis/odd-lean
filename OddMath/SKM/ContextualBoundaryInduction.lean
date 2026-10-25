import OddMath.SKM.MateN
import Mathlib.Order.WellFounded

/-! The terminating boundary induction for contextual sorting.
The local coefficient comparisons are supplied separately, at the unchanged
global external weight. Only same-colour deletion components are requested. -/
namespace OddMath.SKM.ContextualBoundary
variable {I : Type*}

def signed (e : Bool) (a : List I) : List (Letter I) := a.map (fun i => (e, i))
def countSign (e : Bool) (a : List (Letter I)) : ℕ := a.countP (fun x => x.1 == e)
def inversions (e : Bool) : List (Letter I) → ℕ
  | [] => 0
  | x :: a => inversions e a + if x.1 == e then 0 else countSign e a

theorem countSign_append (e : Bool) (a b : List (Letter I)) :
    countSign e (a ++ b) = countSign e a + countSign e b := by
  simp [countSign]

theorem inversions_append (e : Bool) (a b : List (Letter I)) :
    inversions e (a ++ b) = inversions e a + inversions e b + countSign (!e) a * countSign e b := by
  induction a with
  | nil => simp [inversions, countSign]
  | cons x a ih =>
    obtain ⟨s, i⟩ := x
    cases s <;> cases e <;> simp [inversions, countSign, ih, Nat.add_mul] <;> omega

/-- Every word is sorted, or contains an adjacent opposite-order pair. -/
theorem sorted_or_adjacent (e : Bool) (a : List (Letter I)) :
    (∃ u v, a = signed e u ++ signed (!e) v) ∨
    ∃ P Q i j, a = P ++ (!e, i) :: (e, j) :: Q := by
  induction a with
  | nil => exact Or.inl ⟨[], [], rfl⟩
  | cons x a ih =>
    obtain ⟨s, i⟩ := x
    rcases ih with ⟨u, v, rfl⟩ | ⟨P, Q, j, k, rfl⟩
    · by_cases hs : s = e
      · subst s
        exact Or.inl ⟨i :: u, v, rfl⟩
      · have hs' : s = !e := by cases s <;> cases e <;> simp_all
        subst s
        cases u with
        | nil => exact Or.inl ⟨[], i :: v, rfl⟩
        | cons j u => exact Or.inr ⟨[], signed e u ++ signed (!e) v, i, j, rfl⟩
    · exact Or.inr ⟨(s, i) :: P, Q, j, k, rfl⟩

/-- An adjacent sorting move decreases the inversion count by exactly one,
with arbitrary left and right contexts and arbitrary colors. -/
theorem inversions_swap (e : Bool) (P Q : List (Letter I)) (i j : I) :
    inversions e (P ++ (!e, i) :: (e, j) :: Q) =
      inversions e (P ++ (e, j) :: (!e, i) :: Q) + 1 := by
  rw [inversions_append, inversions_append]
  cases e <;> simp [inversions, countSign] <;> omega

/-- Global boundary reduction from sorted boundaries and actual contextual
local descent. The residual premise is required only for equal colors.
The proof is lexicographic in total boundary length and inversion sum. -/
theorem boundary_induction (P : List (Letter I) → List (Letter I) → Prop)
    (hsorted : ∀ u d e v, P (signed true u ++ signed false d) (signed false e ++ signed true v))
    (hsource : ∀ L Q i j b,
      P (L ++ (true, j) :: (false, i) :: Q) b →
      (i = j → P (L ++ Q) b) → P (L ++ (false, i) :: (true, j) :: Q) b)
    (htarget : ∀ a L Q i j,
      P a (L ++ (false, j) :: (true, i) :: Q) →
      (i = j → P a (L ++ Q)) → P a (L ++ (true, i) :: (false, j) :: Q)) :
    ∀ a b, P a b := by
  have H : ∀ n m a b, a.length + b.length = n →
      inversions true a + inversions false b = m → P a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro m
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        intro a b hlen hinv
        rcases sorted_or_adjacent true a with ⟨u, d, rfl⟩ | ⟨L, Q, i, j, rfl⟩
        · rcases sorted_or_adjacent false b with ⟨e, v, rfl⟩ | ⟨L, Q, i, j, rfl⟩
          · exact hsorted u d e v
          · simp only [Bool.not_true, Bool.not_false] at hlen hinv ⊢
            apply htarget
            · apply ihm (inversions true (signed true u ++ signed false d) +
                inversions false (L ++ (false, j) :: (true, i) :: Q))
              · have hs := inversions_swap false L Q i j
                simp only [Bool.not_false] at hs
                omega
              · simp only [List.length_append, List.length_cons] at hlen ⊢
                omega
              · rfl
            · intro _
              apply ihn ((signed true u ++ signed false d).length + (L ++ Q).length)
              · simp only [List.length_append, List.length_cons] at hlen ⊢
                omega
              · rfl
              · rfl
        · simp only [Bool.not_true] at hlen hinv ⊢
          apply hsource
          · apply ihm (inversions true (L ++ (true, j) :: (false, i) :: Q) + inversions false b)
            · have hs := inversions_swap true L Q i j
              simp only [Bool.not_true] at hs
              omega
            · simp only [List.length_append, List.length_cons] at hlen ⊢
              omega
            · rfl
          · intro _
            apply ihn ((L ++ Q).length + b.length)
            · simp only [List.length_append, List.length_cons] at hlen ⊢
              omega
            · rfl
            · rfl
  intro a b
  exact H (a.length + b.length) (inversions true a + inversions false b) a b rfl rfl

end OddMath.SKM.ContextualBoundary

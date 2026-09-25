import OddMath.Frontier.TableauRowStep

/-!
# Rightmost-strict reverse row bumping

Fulton, Young Tableaux, §1.1, printed p.8: reverse bumping selects
"the entry farthest to the right which is strictly less than y".
This module proves the two local row laws only, not total upward recursion.
-/
namespace OddMath.Frontier.TableauReverseRow

open TableauSign TableauEvaluation TableauRowStep

/-- Recurse on the tail first; replace the rightmost letter strictly below b. -/
def reverseStep (n : ℕ) (w : List (Fin n)) (b : Fin n) :
    Option (List (Fin n) × Fin n × ℕ) :=
  match w with
  | [] => none
  | x :: xs =>
    match reverseStep n xs b with
    | some (v,a,c) => some (x :: v,a,c+1)
    | none => if x < b then some (b :: xs,x,0) else none

theorem reverseStep_none (n : ℕ) (w : List (Fin n)) (b : Fin n) :
    reverseStep n w b = none ↔ ∀ x ∈ w, b ≤ x := by
  induction w with
  | nil => simp [reverseStep]
  | cons x xs ih =>
    cases he : reverseStep n xs b with
    | none =>
      have ht := ih.mp he
      simp [reverseStep, he, ht, not_lt]
      exact fun _ => ht
    | some t =>
      have ht : ¬ (∀ y ∈ xs, b ≤ y) := by
        intro h
        rw [ih.mpr h] at he
        cases he
      rcases t with ⟨v,a,c⟩
      simp [reverseStep, he, ht]

theorem reverseStep_split (n : ℕ) (u v : List (Fin n)) (a b : Fin n)
    (hab : a < b) (hv : ∀ x ∈ v, b ≤ x) :
    reverseStep n (u ++ (a :: v)) b = some (u ++ (b :: v),a,u.length) := by
  induction u with
  | nil => simp [reverseStep, (reverseStep_none n v b).mpr hv, hab]
  | cons x u ih => simp [reverseStep, ih]

theorem reverseStep_spec (n : ℕ) (w v : List (Fin n)) (b a : Fin n) (c : ℕ)
    (h : reverseStep n w b = some (v,a,c)) :
    ∃ u z, w = u ++ (a :: z) ∧ v = u ++ (b :: z) ∧ c = u.length ∧
      a < b ∧ (∀ x ∈ z, b ≤ x) := by
  induction w generalizing v a c with
  | nil => simp [reverseStep] at h
  | cons x xs ih =>
    cases he : reverseStep n xs b with
    | none =>
      by_cases hx : x < b
      · simp only [reverseStep, he, hx, if_true, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl,rfl⟩
        exact ⟨[],xs,rfl,rfl,rfl,hx,(reverseStep_none n xs b).mp he⟩
      · simp [reverseStep, he, hx] at h
    | some t =>
      rcases t with ⟨v',a',c'⟩
      simp only [reverseStep, he, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      obtain ⟨u,z,hw,hv,hc,hab,hz⟩ := ih v' a' c' he
      refine ⟨x :: u,z,?_,?_,?_,hab,hz⟩
      · simp only [List.cons_append, hw]
      · simp only [List.cons_append, hv]
      · simp only [List.length_cons, hc]

theorem reverseStep_sorted (n : ℕ) (w v : List (Fin n)) (b a : Fin n) (c : ℕ)
    (hs : w.Sorted (· ≤ ·)) (h : reverseStep n w b = some (v,a,c)) :
    v.Sorted (· ≤ ·) := by
  obtain ⟨u,z,rfl,rfl,_,hab,hz⟩ := reverseStep_spec n w v b a c h
  have hp := List.pairwise_append.mp hs
  have ht := List.pairwise_cons.mp hp.2.1
  apply List.pairwise_append.mpr
  refine ⟨hp.1, List.pairwise_cons.mpr ⟨hz,ht.2⟩, ?_⟩
  intro x hx y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact (hp.2.2 x hx a (by simp)).trans hab.le
  · exact hp.2.2 x hx y (by simp [hy])

theorem reverse_after_forward (n : ℕ) (w : List (Fin n)) (a : Fin n)
    (hs : w.Sorted (· ≤ ·)) :
    match firstGreater n w a with
    | .append _ => True
    | .bump u b v _ _ _ => reverseStep n (u ++ (a :: v)) b = some (w,a,u.length) := by
  cases firstGreater n w a with
  | append _ => trivial
  | bump u b v hw _ hab =>
    have hv := (List.pairwise_cons.mp (List.pairwise_append.mp (hw ▸ hs)).2.1).1
    simpa only [hw] using reverseStep_split n u v a b hab hv

/-- The installed left-to-right selector finds precisely this strict split. -/
private theorem firstGreater_split (n : ℕ) (u v : List (Fin n)) (a b : Fin n)
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    match firstGreater n (u ++ (b :: v)) a with
    | .append _ => False
    | .bump s d t _ _ _ => s = u ∧ d = b ∧ t = v := by
  induction u with
  | nil => simp [firstGreater, hab]
  | cons x u ih =>
    have hx : ¬ a < x := not_lt.mpr (hu x (by simp))
    have hu' : ∀ y ∈ u, y ≤ a := fun y hy => hu y (by simp [hy])
    have hi := ih hu'
    simp only [List.cons_append, firstGreater, hx, dite_false]
    cases he : firstGreater n (u ++ (b :: v)) a with
    | append _ =>
      simp only [he] at hi
    | bump s d t _ _ _ =>
      simp only [he] at hi
      obtain ⟨rfl,rfl,rfl⟩ := hi
      exact ⟨rfl,rfl,rfl⟩

theorem forward_after_reverse (n : ℕ) (w v : List (Fin n)) (b a : Fin n) (c : ℕ)
    (hs : w.Sorted (· ≤ ·)) (h : reverseStep n w b = some (v,a,c)) :
    match firstGreater n v a with
    | .append _ => False
    | .bump u d z _ _ _ => u ++ (a :: z) = w ∧ d = b ∧ u.length = c := by
  obtain ⟨u,z,rfl,rfl,rfl,hab,_⟩ := reverseStep_spec n w v b a c h
  have hp := List.pairwise_append.mp hs
  have hu : ∀ x ∈ u, x ≤ a := fun x hx => hp.2.2 x hx a (by simp)
  have hi := firstGreater_split n u z a b hu hab
  cases he : firstGreater n (u ++ (b :: z)) a with
  | append _ =>
    simp only [he] at hi
  | bump s d t _ _ _ =>
    simp only [he] at hi
    obtain ⟨rfl,rfl,rfl⟩ := hi
    exact ⟨rfl,rfl,rfl⟩

theorem tableau_reverse_after_forward (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ) (a : Fin n) :
    match firstGreater n (row n T hT r) a with
    | .append _ => True
    | .bump u b v _ _ _ =>
      reverseStep n (u ++ (a :: v)) b = some (row n T hT r,a,u.length) :=
  by
    have h := reverse_after_forward n (row n T hT r) a (row_sorted n μ T hT r)
    cases he : firstGreater n (row n T hT r) a with
    | append _ => trivial
    | bump _ _ _ _ _ _ => simpa only [he] using h

theorem tableau_forward_after_reverse (n : ℕ) (μ : YoungDiagram)
    (T : PositiveTableau μ) (hT : InAlphabet n T) (r : ℕ)
    (v : List (Fin n)) (b a : Fin n) (c : ℕ)
    (h : reverseStep n (row n T hT r) b = some (v,a,c)) :
    match firstGreater n v a with
    | .append _ => False
    | .bump u d z _ _ _ => u ++ (a :: z) = row n T hT r ∧ d = b ∧ u.length = c :=
  forward_after_reverse n (row n T hT r) v b a c (row_sorted n μ T hT r) h

end OddMath.Frontier.TableauReverseRow

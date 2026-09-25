import OddMath.Frontier.EKClassicalPlacticControls
import OddMath.Frontier.TableauWordInsertion
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.GroupTheory.Congruence.Defs

/-!
# EK Theorem 4.1: the classical (even) plactic monoid — Knuth normal form

Ellis–Khovanov arXiv:1107.5610v2, p.31, Sec. 4.1, relations (4.1) and Theorem 4.1
(cited from Fulton, *Young Tableaux*, Sec. 2.1). Objects (`bump1`, `ins`, `insW`, `P`,
`readR`, `KStep`, `KnuthEquiv`) are the executable ones fixed in
`EKClassicalPlacticControls`, compiled first.

Core list-level results:
* `knuth_readR_P`   : every word `w` is Knuth-equivalent to `readR (P w)` (existence);
* `P_eq_of_knuth`   : Knuth-equivalent words have the same insertion tableau;
* `P_readR`         : `P (readR rs) = rs` for every valid tableau `rs` (uniqueness).
-/

namespace OddMath.Frontier.EKClassicalPlactic

/-! ## Row insertion lemmas -/

@[simp] theorem bump1_nil (a : ℕ) : bump1 [] a = ([a], none) := rfl

theorem bump1_cons_lt {x a : ℕ} (l : List ℕ) (h : a < x) :
    bump1 (x :: l) a = (a :: l, some x) := by
  simp [bump1, h]

theorem bump1_cons_le {x a : ℕ} (l : List ℕ) (h : x ≤ a) :
    bump1 (x :: l) a = (x :: (bump1 l a).1, (bump1 l a).2) := by
  simp [bump1, Nat.not_lt.mpr h]

theorem bump1_append_le {a : ℕ} (A l : List ℕ) (h : ∀ p ∈ A, p ≤ a) :
    bump1 (A ++ l) a = (A ++ (bump1 l a).1, (bump1 l a).2) := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    have hp := h p List.mem_cons_self
    rw [List.cons_append, bump1_cons_le _ hp, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

theorem bump1_le_all {a : ℕ} (A : List ℕ) (h : ∀ p ∈ A, p ≤ a) :
    bump1 A a = (A ++ [a], none) := by
  simpa using bump1_append_le A [] h

/-- Exact description of one row insertion. -/
theorem bump1_spec (R : List ℕ) (a : ℕ) :
    ((∀ p ∈ R, p ≤ a) ∧ bump1 R a = (R ++ [a], none)) ∨
    (∃ u b v, R = u ++ b :: v ∧ (∀ p ∈ u, p ≤ a) ∧ a < b ∧
      bump1 R a = (u ++ a :: v, some b)) := by
  induction R with
  | nil => left; simp
  | cons x xs ih =>
    by_cases h : a < x
    · right; exact ⟨[], x, xs, rfl, by simp, h, bump1_cons_lt _ h⟩
    · have hx : x ≤ a := Nat.le_of_not_lt h
      rw [bump1_cons_le _ hx]
      rcases ih with ⟨hall, he⟩ | ⟨u, b, v, hs, hu, hab, he⟩
      · left
        refine ⟨?_, by rw [he]; rfl⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hx
        · exact hall p hp
      · right
        refine ⟨x :: u, b, v, by rw [hs]; rfl, ?_, hab, by rw [he]; rfl⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hx
        · exact hu p hp

/-- A weakly increasing row splits at any threshold. -/
theorem sorted_split (R : List ℕ) (hR : R.Sorted (· ≤ ·)) (t : ℕ) :
    ∃ L G, R = L ++ G ∧ (∀ p ∈ L, p ≤ t) ∧ (∀ q ∈ G, t < q) ∧
      L.Sorted (· ≤ ·) ∧ G.Sorted (· ≤ ·) := by
  induction R with
  | nil => exact ⟨[], [], rfl, by simp, by simp, List.sorted_nil, List.sorted_nil⟩
  | cons r R ih =>
    obtain ⟨hr, hR'⟩ := List.sorted_cons.mp hR
    by_cases h : r ≤ t
    · obtain ⟨L, G, hs, hL, hG, hLs, hGs⟩ := ih hR'
      refine ⟨r :: L, G, by rw [hs]; rfl, ?_, hG, ?_, hGs⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact h
        · exact hL p hp
      · refine List.sorted_cons.mpr ⟨fun p hp => hr p ?_, hLs⟩
        rw [hs]; exact List.mem_append_left _ hp
    · refine ⟨[], r :: R, rfl, by simp, ?_, List.sorted_nil, hR⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · omega
      · have := hr q hq; omega

theorem bump1_sorted (R : List ℕ) (hR : R.Sorted (· ≤ ·)) (a : ℕ) :
    (bump1 R a).1.Sorted (· ≤ ·) := by
  obtain ⟨L, G, rfl, hL, hG, hLs, hGs⟩ := sorted_split R hR a
  rw [bump1_append_le L G hL]
  rcases G with _ | ⟨g, G⟩
  · simp only [bump1_nil]
    refine List.pairwise_append.mpr ⟨hLs, List.sorted_singleton _, ?_⟩
    intro p hp q hq
    rw [List.mem_singleton.mp hq]; exact hL p hp
  · have hg := hG g List.mem_cons_self
    rw [bump1_cons_lt _ hg]
    obtain ⟨hg', hGs'⟩ := List.sorted_cons.mp hGs
    refine List.pairwise_append.mpr ⟨hLs, List.sorted_cons.mpr ⟨?_, hGs'⟩, ?_⟩
    · intro q hq; have := hg' q hq; omega
    · intro p hp q hq
      have := hL p hp
      rcases List.mem_cons.mp hq with rfl | hq
      · exact this
      · have := hG q (List.mem_cons_of_mem _ hq); omega

/-- All rows weakly increasing. -/
def RowsSorted (rs : List (List ℕ)) : Prop := ∀ R ∈ rs, R.Sorted (· ≤ ·)

theorem ins_sorted (rs : List (List ℕ)) (h : RowsSorted rs) (a : ℕ) : RowsSorted (ins rs a) := by
  induction rs generalizing a with
  | nil => intro R hR; simp [ins] at hR; subst hR; exact List.sorted_singleton _
  | cons R rs ih =>
    have hR := h R List.mem_cons_self
    have hrs : RowsSorted rs := fun S hS => h S (List.mem_cons_of_mem _ hS)
    intro S hS
    simp only [ins] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact bump1_sorted R hR a
    · cases hb : (bump1 R a).2 with
      | none => rw [hb] at hS; exact hrs S hS
      | some b => rw [hb] at hS; exact ih hrs b S hS

theorem insW_sorted (rs : List (List ℕ)) (h : RowsSorted rs) (w : List ℕ) :
    RowsSorted (insW rs w) := by
  induction w generalizing rs with
  | nil => exact h
  | cons a w ih => exact ih _ (ins_sorted rs h a)

theorem insW_append (rs : List (List ℕ)) (u v : List ℕ) :
    insW rs (u ++ v) = insW (insW rs u) v := by
  simp [insW, List.foldl_append]

theorem P_sorted (w : List ℕ) : RowsSorted (P w) := insW_sorted [] (by simp [RowsSorted]) w

/-! ## Row-by-row decomposition of insertion -/

/-- Insert a word into one row; returns the new row and the word of bumped letters. -/
def rowIns : List ℕ → List ℕ → List ℕ × List ℕ
  | R, [] => (R, [])
  | R, a :: w => ((rowIns (bump1 R a).1 w).1, (bump1 R a).2.toList ++ (rowIns (bump1 R a).1 w).2)

theorem insW_cons_rows (R : List ℕ) (rs : List (List ℕ)) (w : List ℕ) :
    insW (R :: rs) w = (rowIns R w).1 :: insW rs (rowIns R w).2 := by
  induction w generalizing R rs with
  | nil => rfl
  | cons a w ih =>
    change insW (ins (R :: rs) a) w = _
    simp only [ins, rowIns]
    rw [ih, insW_append]
    congr 2
    cases (bump1 R a).2 <;> rfl

theorem rowIns_length (R w : List ℕ) : (rowIns R w).2.length ≤ w.length := by
  induction w generalizing R with
  | nil => simp [rowIns]
  | cons a w ih =>
    simp only [rowIns, List.length_append, List.length_cons]
    have := ih (bump1 R a).1
    cases (bump1 R a).2 <;> simp <;> omega

/-! ## The one-row Knuth lemma (case analysis on the four threshold segments) -/

/-- The four printed moves on a three-letter word (both directions of (K′) and (K″)). -/
def E3 : List ℕ → List ℕ → Prop
  | [a, b, c], [a', b', c'] =>
      (a' = b ∧ b' = a ∧ c' = c ∧ ((a ≤ c ∧ c < b) ∨ (b ≤ c ∧ c < a))) ∨
      (a' = a ∧ b' = c ∧ c' = b ∧ ((c < a ∧ a ≤ b) ∨ (b < a ∧ a ≤ c)))
  | _, _ => False

theorem E3_symm {w w' : List ℕ} (h : E3 w w') : E3 w' w := by
  match w, w', h with
  | [a, b, c], [a', b', c'], h => simp only [E3] at h ⊢; omega

theorem E3_length {w w' : List ℕ} (h : E3 w w') : w.length = 3 := by
  match w, w', h with
  | [_, _, _], [_, _, _], _ => rfl

/-- Four-segment decomposition of a weakly increasing row at thresholds `x ≤ y ≤ z`. -/
theorem sorted_split4 (R : List ℕ) (hR : R.Sorted (· ≤ ·)) (x y z : ℕ) :
    ∃ A B C D, R = A ++ (B ++ (C ++ D)) ∧ (∀ p ∈ A, p ≤ x) ∧
      (∀ p ∈ B, x < p ∧ p ≤ y) ∧ (∀ p ∈ C, x < p ∧ y < p ∧ p ≤ z) ∧
      (∀ p ∈ D, x < p ∧ y < p ∧ z < p) ∧ C.Sorted (· ≤ ·) ∧ D.Sorted (· ≤ ·) := by
  obtain ⟨A, G1, rfl, hA, hG1, _, hG1s⟩ := sorted_split R hR x
  obtain ⟨B, G2, rfl, hB, hG2, _, hG2s⟩ := sorted_split G1 hG1s y
  obtain ⟨C, D, rfl, hC, hD, hCs, hDs⟩ := sorted_split G2 hG2s z
  refine ⟨A, B, C, D, rfl, hA, ?_, ?_, ?_, hCs, hDs⟩
  · intro p hp; exact ⟨hG1 p (by simp [hp]), hB p hp⟩
  · intro p hp; exact ⟨hG1 p (by simp [hp]), hG2 p (by simp [hp]), hC p hp⟩
  · intro p hp; exact ⟨hG1 p (by simp [hp]), hG2 p (by simp [hp]), hD p hp⟩

section RowMacros
set_option hygiene false

/-- Discharger for the row case analysis: exact segment facts or linear arithmetic. -/
macro "ek_row_disch" : tactic => `(tactic| first | assumption | omega)

/-- Split one segment fact `∀ p ∈ b :: L, _` into its head fact and its tail fact. -/
macro "ek_split " h:ident : tactic => `(tactic|
  ((try simp only [List.forall_mem_cons] at $h:ident) <;> (try obtain ⟨_, $h:ident⟩ := $h:ident)))

/-- Exhaustive case split on the (non)emptiness of segments `B`, `C`, `D`. -/
macro "ek_row_cases" : tactic => `(tactic|
  (have hAy : ∀ p ∈ A, p ≤ y := fun p hp => by have := hA p hp; omega
   have hAz : ∀ p ∈ A, p ≤ z := fun p hp => by have := hA p hp; omega
   have hBy : ∀ p ∈ B, p ≤ y := fun p hp => (hB p hp).2
   have hBz : ∀ p ∈ B, p ≤ z := fun p hp => by have := hB p hp; omega
   have hCz : ∀ p ∈ C, p ≤ z := fun p hp => (hC p hp).2.2
   rcases B with _ | ⟨b, _ | ⟨b', B⟩⟩ <;> rcases C with _ | ⟨c, _ | ⟨c', C⟩⟩ <;>
    rcases D with _ | ⟨d, _ | ⟨d', D⟩⟩ <;>
    ek_split hB <;> ek_split hBy <;> ek_split hBz <;> ek_split hC <;> ek_split hCz <;>
    ek_split hD <;>
    ek_split hB <;> ek_split hBy <;> ek_split hBz <;> ek_split hC <;> ek_split hCz <;>
    ek_split hD <;>
    (try simp only [List.sorted_cons, List.forall_mem_cons] at hCs) <;>
    (try simp only [List.sorted_cons, List.forall_mem_cons] at hDs) <;>
    (try obtain ⟨⟨_, -⟩, -⟩ := hCs) <;> (try obtain ⟨⟨_, -⟩, -⟩ := hDs) <;>
    simp (disch := ek_row_disch) only [rowIns, bump1_append_le, bump1_le_all, bump1_cons_lt, bump1_cons_le,
      bump1_nil, List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
      Option.toList_some, Option.toList_none, E3, true_and, and_true, true_or, or_true,
      List.cons.injEq] <;>
    omega))

end RowMacros

/-- One-row lemma for (K″): `xzy → zxy`, `x ≤ y < z`. -/
theorem row_K2 (R : List ℕ) (hR : R.Sorted (· ≤ ·)) {x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) :
    (rowIns R [x, z, y]).1 = (rowIns R [z, x, y]).1 ∧
      ((rowIns R [x, z, y]).2 = (rowIns R [z, x, y]).2 ∨
        E3 (rowIns R [x, z, y]).2 (rowIns R [z, x, y]).2) := by
  obtain ⟨A, B, C, D, rfl, hA, hB, hC, hD, hCs, hDs⟩ := sorted_split4 R hR x y z
  ek_row_cases

/-- One-row lemma for (K′): `yzx → yxz`, `x < y ≤ z`. -/
theorem row_K1 (R : List ℕ) (hR : R.Sorted (· ≤ ·)) {x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) :
    (rowIns R [y, z, x]).1 = (rowIns R [y, x, z]).1 ∧
      ((rowIns R [y, z, x]).2 = (rowIns R [y, x, z]).2 ∨
        E3 (rowIns R [y, z, x]).2 (rowIns R [y, x, z]).2) := by
  obtain ⟨A, B, C, D, rfl, hA, hB, hC, hD, hCs, hDs⟩ := sorted_split4 R hR x y z
  ek_row_cases

theorem row_E3 (R : List ℕ) (hR : R.Sorted (· ≤ ·)) {w w' : List ℕ} (h : E3 w w') :
    (rowIns R w).1 = (rowIns R w').1 ∧
      ((rowIns R w).2 = (rowIns R w').2 ∨ E3 (rowIns R w).2 (rowIns R w').2) := by
  match w, w', h with
  | [a, b, c], [a', b', c'], h =>
    simp only [E3] at h
    rcases h with ⟨rfl, rfl, rfl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨rfl, rfl, rfl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact row_K2 R hR h1 h2
    · have := row_K2 R hR h1 h2
      exact ⟨this.1.symm, this.2.imp Eq.symm E3_symm⟩
    · exact row_K1 R hR h1 h2
    · have := row_K1 R hR h1 h2
      exact ⟨this.1.symm, this.2.imp Eq.symm E3_symm⟩

theorem rowIns_nil_length (a : ℕ) (t : List ℕ) : (rowIns [] (a :: t)).2.length ≤ t.length := by
  simp only [rowIns, bump1_nil, Option.toList_none, List.nil_append]
  exact rowIns_length _ _

theorem insW_nil_eq (w : List ℕ) (hw : w ≠ []) : insW [] w = insW [[]] w := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a t => rfl

/-- Insertion is invariant under one printed move, on any list of weakly increasing rows. -/
theorem insW_E3 (rs : List (List ℕ)) (hrs : RowsSorted rs) {w w' : List ℕ} (h : E3 w w') :
    insW rs w = insW rs w' := by
  induction rs generalizing w w' with
  | nil =>
    have hl := E3_length h
    have hl' := E3_length (E3_symm h)
    rw [insW_nil_eq w (by rintro rfl; simp at hl), insW_nil_eq w' (by rintro rfl; simp at hl'),
      insW_cons_rows, insW_cons_rows]
    obtain ⟨h1, h2⟩ := row_E3 [] List.sorted_nil h
    rw [h1]
    rcases h2 with h2 | h2
    · rw [h2]
    · exfalso
      have h3 := E3_length h2
      match w, hl with
      | a :: t, hl =>
        have := rowIns_nil_length a t
        simp only [List.length_cons] at hl
        omega
  | cons R rs ih =>
    have hR := hrs R List.mem_cons_self
    have hrs' : RowsSorted rs := fun S hS => hrs S (List.mem_cons_of_mem _ hS)
    rw [insW_cons_rows, insW_cons_rows]
    obtain ⟨h1, h2⟩ := row_E3 R hR h
    rw [h1]
    rcases h2 with h2 | h2
    · rw [h2]
    · rw [ih hrs' h2]

theorem E3_of_KStep_core {x y z : ℕ} :
    (x < y → y ≤ z → E3 [y, z, x] [y, x, z]) ∧ (x ≤ y → y < z → E3 [x, z, y] [z, x, y]) := by
  constructor
  · intro h1 h2; exact Or.inr ⟨rfl, rfl, rfl, Or.inl ⟨h1, h2⟩⟩
  · intro h1 h2; exact Or.inl ⟨rfl, rfl, rfl, Or.inl ⟨h1, h2⟩⟩

theorem insW_KStep (rs : List (List ℕ)) (hrs : RowsSorted rs) {w w' : List ℕ} (h : KStep w w') :
    insW rs w = insW rs w' := by
  obtain ⟨u, v, x, y, z, ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩⟩ := h
  · rw [insW_append, insW_append, insW_append, insW_append,
      insW_E3 _ (insW_sorted rs hrs u) (E3_of_KStep_core.1 h1 h2)]
  · rw [insW_append, insW_append, insW_append, insW_append,
      insW_E3 _ (insW_sorted rs hrs u) (E3_of_KStep_core.2 h1 h2)]

/-- Knuth-equivalent words have the same insertion tableau. -/
theorem P_eq_of_knuth {w w' : List ℕ} (h : KnuthEquiv w w') : P w = P w' := by
  induction h with
  | rel a b hab => exact insW_KStep [] (by simp [RowsSorted]) hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Knuth equivalence is a congruence; existence of the tableau word -/

theorem KStep_context {w w' : List ℕ} (h : KStep w w') (p s : List ℕ) :
    KStep (p ++ w ++ s) (p ++ w' ++ s) := by
  obtain ⟨u, v, x, y, z, ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩⟩ := h
  · exact ⟨p ++ u, v ++ s, x, y, z, Or.inl ⟨h1, h2, by simp, by simp⟩⟩
  · exact ⟨p ++ u, v ++ s, x, y, z, Or.inr ⟨h1, h2, by simp, by simp⟩⟩

theorem knuth_context {w w' : List ℕ} (h : KnuthEquiv w w') (p s : List ℕ) :
    KnuthEquiv (p ++ w ++ s) (p ++ w' ++ s) := by
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (KStep_context hab p s)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem knuth_refl (w : List ℕ) : KnuthEquiv w w := Relation.EqvGen.refl _

theorem knuth_symm {w w' : List ℕ} (h : KnuthEquiv w w') : KnuthEquiv w' w :=
  Relation.EqvGen.symm _ _ h

theorem knuth_trans {a b c : List ℕ} (h₁ : KnuthEquiv a b) (h₂ : KnuthEquiv b c) :
    KnuthEquiv a c := Relation.EqvGen.trans _ _ _ h₁ h₂

theorem knuth_K1 {x y z : ℕ} (h1 : x < y) (h2 : y ≤ z) (p s : List ℕ) :
    KnuthEquiv (p ++ y :: z :: x :: s) (p ++ y :: x :: z :: s) :=
  Relation.EqvGen.rel _ _ ⟨p, s, x, y, z, Or.inl ⟨h1, h2, by simp, by simp⟩⟩

theorem knuth_K2 {x y z : ℕ} (h1 : x ≤ y) (h2 : y < z) (p s : List ℕ) :
    KnuthEquiv (p ++ x :: z :: y :: s) (p ++ z :: x :: y :: s) :=
  Relation.EqvGen.rel _ _ ⟨p, s, x, y, z, Or.inr ⟨h1, h2, by simp, by simp⟩⟩

/-- Move `a` left through a weakly increasing run `c :: v` of letters `> a`, using (K′). -/
theorem knuth_move_right_part (a : ℕ) :
    ∀ (c : ℕ) (v : List ℕ), a < c → (c :: v).Sorted (· ≤ ·) →
      KnuthEquiv (c :: v ++ [a]) (c :: a :: v) := by
  intro c v
  induction v generalizing c with
  | nil => intro _ _; exact knuth_refl _
  | cons d v ih =>
    intro hac hs
    obtain ⟨hcd, hs'⟩ := List.sorted_cons.mp hs
    have hcd' := hcd d List.mem_cons_self
    have h1 := knuth_context (ih d (by omega) hs') [c] []
    simp only [List.singleton_append, List.append_nil, List.cons_append] at h1
    refine knuth_trans h1 ?_
    simpa using knuth_K1 (x := a) (y := c) (z := d) hac hcd' [] v

/-- Move `b` left through a weakly increasing run `u` of letters `≤ t < b`, using (K″). -/
theorem knuth_move_left_part (b t : ℕ) (rest : List ℕ) (htb : t < b) :
    ∀ (u : List ℕ), u.Sorted (· ≤ ·) → (∀ p ∈ u, p ≤ t) →
      KnuthEquiv (u ++ b :: t :: rest) (b :: (u ++ t :: rest)) := by
  intro u
  induction u with
  | nil => intro _ _; exact knuth_refl _
  | cons p u ih =>
    intro hs hu
    obtain ⟨hpu, hs'⟩ := List.sorted_cons.mp hs
    have hpt := hu p List.mem_cons_self
    have h1 := knuth_context (ih hs' (fun q hq => hu q (List.mem_cons_of_mem _ hq))) [p] []
    simp only [List.singleton_append, List.append_nil, List.cons_append] at h1
    refine knuth_trans h1 ?_
    -- next letter after `b` is the head `q` of `u ++ t :: rest`, with `p ≤ q < b`
    cases u with
    | nil =>
      simpa using knuth_K2 (x := p) (y := t) (z := b) hpt htb [] rest
    | cons q u =>
      have hpq := hpu q List.mem_cons_self
      have hqt := hu q (by simp)
      simpa using knuth_K2 (x := p) (y := q) (z := b) hpq (by omega) [] (u ++ t :: rest)

/-- Fulton's row bumping in the plactic monoid: `R · a ≡ b · R'`. -/
theorem knuth_row_bump (u v : List ℕ) (a b : ℕ) (hs : (u ++ b :: v).Sorted (· ≤ ·))
    (hu : ∀ p ∈ u, p ≤ a) (hab : a < b) :
    KnuthEquiv (u ++ b :: v ++ [a]) (b :: (u ++ a :: v)) := by
  have hus : u.Sorted (· ≤ ·) := (List.pairwise_append.mp hs).1
  have hbv : (b :: v).Sorted (· ≤ ·) := (List.pairwise_append.mp hs).2.1
  have h1 := knuth_context (knuth_move_right_part a b v hab hbv) u []
  simp only [List.append_nil, List.append_assoc] at h1
  refine knuth_trans (by simpa using h1) ?_
  exact knuth_move_left_part b a v hab u hus hu

/-- One insertion step is a Knuth equivalence of row words. -/
theorem knuth_ins (rs : List (List ℕ)) (hrs : RowsSorted rs) (a : ℕ) :
    KnuthEquiv (readR rs ++ [a]) (readR (ins rs a)) := by
  induction rs generalizing a with
  | nil => exact knuth_refl _
  | cons R rs ih =>
    have hR := hrs R List.mem_cons_self
    have hrs' : RowsSorted rs := fun S hS => hrs S (List.mem_cons_of_mem _ hS)
    simp only [readR, ins, List.reverse_cons, List.flatten_append, List.flatten_singleton] at ih ⊢
    rcases bump1_spec R a with ⟨_, he⟩ | ⟨u, b, v, hs, hu, hab, he⟩
    · rw [he]; simp only [List.append_assoc]; exact knuth_refl _
    · rw [he]
      simp only
      subst hs
      have h1 := knuth_context (knuth_row_bump u v a b hR hu hab) (rs.reverse.flatten) []
      have h2 := knuth_context (ih hrs' b) [] (u ++ a :: v)
      simp only [List.append_nil, List.nil_append, List.append_assoc, List.cons_append,
        List.singleton_append] at h1 h2 ⊢
      exact knuth_trans h1 h2

/-- Existence: every word is Knuth-equivalent to the row word of its insertion tableau. -/
theorem knuth_readR_insW (rs : List (List ℕ)) (hrs : RowsSorted rs) (w : List ℕ) :
    KnuthEquiv (readR rs ++ w) (readR (insW rs w)) := by
  induction w generalizing rs with
  | nil => simpa using knuth_refl (readR rs)
  | cons a w ih =>
    have h1 := knuth_context (knuth_ins rs hrs a) [] w
    simp only [List.nil_append, List.append_assoc, List.singleton_append] at h1
    exact knuth_trans h1 (ih (ins rs a) (ins_sorted rs hrs a))

theorem knuth_readR_P (w : List ℕ) : KnuthEquiv w (readR (P w)) := by
  simpa [readR] using knuth_readR_insW [] (by simp [RowsSorted]) w

/-! ## Uniqueness: insertion recovers a tableau from its row word -/

/-- Column strictness between an upper row and the row below it (lower row not longer). -/
def Dom : List ℕ → List ℕ → Prop
  | _, [] => True
  | [], _ :: _ => False
  | a :: as, b :: bs => a < b ∧ Dom as bs

theorem dom_nil (a : List ℕ) : Dom a [] := by cases a <;> trivial

/-- A semistandard tableau given by its rows, top row first. -/
def Valid : List (List ℕ) → Prop
  | [] => True
  | R :: rs => R ≠ [] ∧ R.Sorted (· ≤ ·) ∧ Dom R (rs.headD []) ∧ Valid rs

/-- Inserting a row `a` into a row `p ++ b` it dominates bumps out exactly `b`. -/
theorem rowIns_dom : ∀ (a b p : List ℕ), a.Sorted (· ≤ ·) → (∀ q ∈ p, ∀ x ∈ a, q ≤ x) →
    Dom a b → rowIns (p ++ b) a = (p ++ a, b) := by
  intro a
  induction a with
  | nil =>
    intro b p _ _ hd
    cases b with
    | nil => simp [rowIns]
    | cons _ _ => exact absurd hd (by simp [Dom])
  | cons x a ih =>
    intro b p hs hp hd
    obtain ⟨hxa, hs'⟩ := List.sorted_cons.mp hs
    have hpx : ∀ q ∈ p, q ≤ x := fun q hq => hp q hq x List.mem_cons_self
    have hp' : ∀ q ∈ p ++ [x], ∀ y ∈ a, q ≤ y := by
      intro q hq y hy
      rcases List.mem_append.mp hq with hq | hq
      · exact hp q hq y (List.mem_cons_of_mem _ hy)
      · rw [List.mem_singleton.mp hq]; exact hxa y hy
    cases b with
    | nil =>
      have h := ih [] (p ++ [x]) hs' hp' (dom_nil a)
      simp only [List.append_nil] at h ⊢
      simp only [rowIns, bump1_le_all p hpx, h, Option.toList_none, List.nil_append,
        List.append_assoc, List.singleton_append]
    | cons c b =>
      obtain ⟨hxc, hd'⟩ := hd
      have h := ih b (p ++ [x]) hs' hp' hd'
      simp only [List.append_assoc, List.singleton_append] at h
      simp only [rowIns, bump1_append_le p _ hpx, bump1_cons_lt _ hxc, h, Option.toList_some,
        List.singleton_append]

theorem insW_row (S : List (List ℕ)) : ∀ R, Valid (R :: S) → insW S R = R :: S := by
  induction S with
  | nil =>
    intro R hv
    obtain ⟨hne, hs, _, _⟩ := hv
    rw [insW_nil_eq R hne, insW_cons_rows]
    have h := rowIns_dom R [] [] hs (by simp) (dom_nil R)
    simp only [List.append_nil, List.nil_append] at h
    rw [h]; rfl
  | cons R' S ih =>
    intro R hv
    obtain ⟨_, hs, hd, hv'⟩ := hv
    rw [insW_cons_rows]
    have h := rowIns_dom R R' [] hs (by simp) hd
    simp only [List.nil_append] at h
    rw [h, ih R' hv']

/-- `P (wr(T)) = T` for every semistandard tableau `T` (rows top first). -/
theorem P_readR : ∀ rs : List (List ℕ), Valid rs → P (readR rs) = rs
  | [], _ => rfl
  | R :: S, hv => by
    have hS : Valid S := hv.2.2.2
    have hr : readR (R :: S) = readR S ++ R := by simp [readR]
    rw [hr, P, insW_append]
    change insW (P (readR S)) R = R :: S
    rw [P_readR S hS]
    exact insW_row S R hv

/-- List-level uniqueness: two tableaux with Knuth-equivalent row words coincide. -/
theorem valid_eq_of_knuth {rs rs' : List (List ℕ)} (h : Valid rs) (h' : Valid rs')
    (hk : KnuthEquiv (readR rs) (readR rs')) : rs = rs' := by
  rw [← P_readR rs h, ← P_readR rs' h', P_eq_of_knuth hk]

/-- Knuth moves permute letters. -/
theorem perm_of_knuth {w w' : List ℕ} (h : KnuthEquiv w w') : w.Perm w' := by
  induction h with
  | rel a b hab =>
    obtain ⟨u, v, x, y, z, ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩⟩ := hab
    · exact ((List.Perm.cons y (List.Perm.swap x z [])).append_left u).append_right v
    · exact ((List.Perm.swap z x [y]).append_left u).append_right v
  | refl => exact List.Perm.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Bridge to the existing tableau objects

`PositiveTableau μ` (positive semistandard tableaux on a Mathlib `YoungDiagram`),
`TableauRowWord.rowWord` (left to right, bottom to top), `TableauRowRecursion.rows`,
`TableauInsertion.insert` / `TableauWordInsertion.run` (existing row insertion, letters
`Fin n`, label `i ↦ i.val + 1`). -/

open TableauSign TableauEvaluation TableauRowRecursion TableauRowStep TableauBumpBoundary

/-- The existing letter labelling `Fin n → ℕ`, `i ↦ i + 1`. -/
def lab {n : ℕ} (i : Fin n) : ℕ := i.val + 1

theorem lab_injective (n : ℕ) : Function.Injective (lab (n := n)) := by
  intro a b h; apply Fin.ext; simp only [lab] at h; omega

theorem lab_le {n : ℕ} {a b : Fin n} : lab a ≤ lab b ↔ a ≤ b := by
  simp only [lab, Fin.le_def]; omega

theorem lab_lt {n : ℕ} {a b : Fin n} : lab a < lab b ↔ a < b := by
  simp only [lab, Fin.lt_def]; omega

/-- Existing one-letter insertion agrees with `ins` under the labelling. -/
theorem runRows_map (n : ℕ) (rs : List (List (Fin n))) (a : Fin n) :
    (runRows n rs a).output.map (List.map lab) = ins (rs.map (List.map lab)) (lab a) := by
  induction rs generalizing a with
  | nil => rfl
  | cons w ws ih =>
    cases hfg : firstGreater n w a with
    | append ha =>
      simp only [runRows, hfg]
      have hle : ∀ p ∈ w.map lab, p ≤ lab a := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact lab_le.mpr (ha q hq)
      simp only [List.map_cons, ins, bump1_le_all _ hle, List.map_append, List.map_nil]
    | bump u b v hs hu hab =>
      simp only [runRows, hfg]
      rw [hs]
      have hle : ∀ p ∈ u.map lab, p ≤ lab a := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact lab_le.mpr (hu q hq)
      simp only [List.map_cons, List.map_append, ins, bump1_append_le _ _ hle,
        bump1_cons_lt _ (lab_lt.mpr hab), ih]

theorem foldl_runRows_map (n : ℕ) (rs : List (List (Fin n))) (w : List (Fin n)) :
    (w.foldl (fun rs a => (runRows n rs a).output) rs).map (List.map lab) =
      insW (rs.map (List.map lab)) (w.map lab) := by
  induction w generalizing rs with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    change insW _ _ = insW (ins _ _) _
    rw [runRows_map]

/-- Rows of the existing chronological insertion. -/
theorem run_rows (n : ℕ) (S : TableauWordInsertion.State n) (w : List (Fin n)) :
    rows n (TableauWordInsertion.run n S w).1.2.1 (TableauWordInsertion.run n S w).1.2.2 =
      w.foldl (fun rs a => (runRows n rs a).output) (rows n S.2.1 S.2.2) := by
  induction w generalizing S with
  | nil => rfl
  | cons a w ih =>
    simp only [TableauWordInsertion.run, List.foldl_cons]
    rw [ih]
    rw [TableauInsertion.insert_rows]

/-- The empty tableau. -/
def emptyTableau : PositiveTableau ⊥ where
  entry := fun _ _ => 0
  row_weak' := fun _ h => absurd h (YoungDiagram.not_mem_bot _)
  col_strict' := fun _ h => absurd h (YoungDiagram.not_mem_bot _)
  zeros' := fun _ => rfl
  positive := fun h => absurd h (YoungDiagram.not_mem_bot _)

theorem emptyTableau_inAlphabet (n : ℕ) : InAlphabet n emptyTableau := by
  intro p hp
  exact absurd (show p ∈ (⊥ : YoungDiagram) from hp) (YoungDiagram.not_mem_bot _)

/-- The empty insertion state. -/
def emptyState (n : ℕ) : TableauWordInsertion.State n :=
  ⟨⊥, ⟨emptyTableau, emptyTableau_inAlphabet n⟩⟩

theorem rows_empty (n : ℕ) : rows n (emptyState n).2.1 (emptyState n).2.2 = [] := by
  have h : (⊥ : YoungDiagram).colLen 0 = 0 := by
    by_contra hne
    exact YoungDiagram.not_mem_bot (0, 0)
      (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hne))
  simp [rows, emptyState, h]

/-- The insertion tableau of a word `w` in the alphabet `Fin n` (labels `1..n`), computed by
the existing insertion `TableauWordInsertion.run` from the empty tableau. -/
noncomputable def insertionTableau (n : ℕ) (w : List (Fin n)) : Σ μ : YoungDiagram, PositiveTableau μ :=
  ⟨(TableauWordInsertion.run n (emptyState n) w).1.1, (TableauWordInsertion.run n (emptyState n) w).1.2.1⟩

theorem insertionTableau_inAlphabet (n : ℕ) (w : List (Fin n)) :
    InAlphabet n (insertionTableau n w).2 := (TableauWordInsertion.run n (emptyState n) w).1.2.2

/-- The rows of the existing insertion tableau are the list-level `P`. -/
theorem insertionTableau_rows (n : ℕ) (w : List (Fin n)) :
    (rows n (insertionTableau n w).2 (insertionTableau_inAlphabet n w)).map (List.map lab) =
      P (w.map lab) := by
  have h := run_rows n (emptyState n) w
  rw [rows_empty] at h
  change (rows n (TableauWordInsertion.run n (emptyState n) w).1.2.1
    (TableauWordInsertion.run n (emptyState n) w).1.2.2).map (List.map lab) = _
  rw [h, foldl_runRows_map]
  rfl

/-- The existing row word is `readR` of the labelled rows. -/
theorem rowWord_eq_readR (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T) :
    TableauRowWord.rowWord T = readR ((rows n T hT).map (List.map lab)) := by
  rw [← rowFinWord_labels n T hT, ← readRows_rows n μ T hT]
  simp [readR, readRows, List.map_flatten, List.map_reverse]
  rfl

theorem dom_of_columnBelow {n : ℕ} :
    ∀ (u l : List (Fin n)), ColumnBelow u l → Dom (u.map lab) (l.map lab)
  | _, [], _ => dom_nil _
  | [], _ :: _, ⟨hlen, _⟩ => absurd hlen (by simp)
  | x :: u, y :: l, ⟨hlen, hc⟩ => by
    refine ⟨lab_lt.mpr (hc 0 (by simp)), dom_of_columnBelow u l ⟨?_, ?_⟩⟩
    · simp only [List.length_cons] at hlen; omega
    · intro c hcl
      have := hc (c + 1) (by simp; omega)
      simpa using this

theorem valid_of_rows {n : ℕ} : ∀ (rs : List (List (Fin n))),
    (∀ w ∈ rs, w.Sorted (· ≤ ·)) →
    (∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) →
    (∀ w ∈ rs, w ≠ []) → Valid (rs.map (List.map lab))
  | [], _, _, _ => trivial
  | R :: S, hs, hc, hn => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hn R List.mem_cons_self
    · exact List.Pairwise.map lab (fun a b h => lab_le.mpr h) (hs R List.mem_cons_self)
    · have h0 := hc 0
      cases S with
      | nil => exact dom_nil _
      | cons R' S => simpa using dom_of_columnBelow R R' (by simpa using h0)
    · exact valid_of_rows S (fun w hw => hs w (List.mem_cons_of_mem _ hw))
        (fun r => by simpa using hc (r + 1)) (fun w hw => hn w (List.mem_cons_of_mem _ hw))

theorem valid_rows {n : ℕ} {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T) :
    Valid ((rows n T hT).map (List.map lab)) := by
  obtain ⟨hs, hc, hn, _, _⟩ := TableauOfRows.genuine_roundtrip n μ T hT
  exact valid_of_rows _ hs hc hn

/-- Equal shapes and entries give equal sigma-tableaux. -/
theorem sigma_eq {μ μ' : YoungDiagram} (T : PositiveTableau μ) (T' : PositiveTableau μ')
    (h : μ = μ') (he : ∀ r c, T.entry r c = T'.entry r c) :
    (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩ := by
  subst h
  obtain ⟨⟨e, _, _, _⟩, _⟩ := T
  obtain ⟨⟨e', _, _, _⟩, _⟩ := T'
  have : e = e' := funext fun r => funext fun c => he r c
  subst this
  rfl

/-- A tableau is determined by its rows. -/
theorem sigma_eq_of_rows (n : ℕ) {μ μ' : YoungDiagram} (T : PositiveTableau μ)
    (T' : PositiveTableau μ') (hT : InAlphabet n T) (hT' : InAlphabet n T')
    (h : rows n T hT = rows n T' hT') :
    (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩ := by
  obtain ⟨hs, hc, hn, hμ, he⟩ := TableauOfRows.genuine_roundtrip n μ T hT
  obtain ⟨hs', hc', hn', hμ', he'⟩ := TableauOfRows.genuine_roundtrip n μ' T' hT'
  refine sigma_eq T T' ?_ ?_
  · rw [← hμ, ← hμ']
    generalize hc = x
    generalize hc' = y
    revert x y
    rw [h]
    intro x y
    rfl
  · intro r c
    rw [← he r c, ← he' r c, TableauOfRows.tableau_entry, TableauOfRows.tableau_entry, h]

/-! ## EK Theorem 4.1 for the existing tableaux -/

theorem le_foldr_max {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.foldr max 0
  | [], ha => absurd ha (by simp)
  | x :: l, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max ha) (le_max_right _ _)

/-- Any tableau whose row word is Knuth-equivalent to `w` has rows `P w` (labelled). -/
theorem rows_eq_P {n : ℕ} {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T)
    {w : List ℕ} (hk : KnuthEquiv w (TableauRowWord.rowWord T)) :
    (rows n T hT).map (List.map lab) = P w := by
  rw [P_eq_of_knuth hk, rowWord_eq_readR n T hT, P_readR _ (valid_rows T hT)]

/-- Letters of a Knuth-equivalent row word bound the tableau entries. -/
theorem inAlphabet_of_knuth {n : ℕ} {μ : YoungDiagram} (T : PositiveTableau μ) {w : List ℕ}
    (hw : ∀ a ∈ w, a ≤ n) (hk : KnuthEquiv w (TableauRowWord.rowWord T)) : InAlphabet n T := by
  intro p hp
  have hm : T.entry p.1 p.2 ∈ TableauRowWord.rowWord T :=
    List.mem_map.mpr ⟨p, (TableauRowWord.mem_rowCells μ p).mpr hp, rfl⟩
  exact hw _ ((perm_of_knuth hk).symm.subset hm)

/-- **Uniqueness half of EK Thm 4.1**: two semistandard tableaux whose row words are
Knuth-equivalent (relations (K′), (K″) exactly as printed) are equal. -/
theorem tableau_eq_of_knuth {μ μ' : YoungDiagram} (T : PositiveTableau μ) (T' : PositiveTableau μ')
    (hk : KnuthEquiv (TableauRowWord.rowWord T) (TableauRowWord.rowWord T')) :
    (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩ := by
  let n := (TableauRowWord.rowWord T).foldr max 0
  have hb : ∀ a ∈ TableauRowWord.rowWord T, a ≤ n := fun a ha => le_foldr_max ha
  have hT := inAlphabet_of_knuth T hb (knuth_refl _)
  have hT' := inAlphabet_of_knuth T' hb hk
  apply sigma_eq_of_rows n T T' hT hT'
  apply List.map_injective_iff.mpr (List.map_injective_iff.mpr (lab_injective n))
  rw [rows_eq_P T hT (knuth_refl _), rows_eq_P T' hT' hk]

/-- **EK Theorem 4.1, insertion form** (alphabet `{1,…,n}` as `Fin n`, label `i ↦ i+1`):
the word `w` is Knuth-equivalent to the row word of its (existing) insertion tableau, and
that tableau is the unique semistandard tableau with this property. -/
theorem theorem_4_1_insertion (n : ℕ) (w : List (Fin n)) :
    KnuthEquiv (w.map lab) (TableauRowWord.rowWord (insertionTableau n w).2) ∧
    ∀ S : Σ μ : YoungDiagram, PositiveTableau μ,
      KnuthEquiv (w.map lab) (TableauRowWord.rowWord S.2) → S = insertionTableau n w := by
  have hex : KnuthEquiv (w.map lab) (TableauRowWord.rowWord (insertionTableau n w).2) := by
    rw [rowWord_eq_readR n _ (insertionTableau_inAlphabet n w), insertionTableau_rows]
    exact knuth_readR_P _
  refine ⟨hex, ?_⟩
  rintro ⟨μ, T⟩ hk
  exact tableau_eq_of_knuth T (insertionTableau n w).2 (knuth_trans (knuth_symm hk) hex)

/-- **EK Theorem 4.1** (arXiv:1107.5610v2, p.31), alphabet `A = ℤ_{>0}`: every word is
equivalent, via relations (K′) and (K″) exactly as printed, to the row word `wr(T)`
(`TableauRowWord.rowWord`) of a unique semistandard tableau `T`. -/
theorem theorem_4_1 (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    ∃! S : Σ μ : YoungDiagram, PositiveTableau μ, KnuthEquiv w (TableauRowWord.rowWord S.2) := by
  let n := w.foldr max 0
  have hb : ∀ a ∈ w, a ≤ n := fun a ha => le_foldr_max ha
  let w' : List (Fin n) := w.attach.map fun a =>
    ⟨a.1 - 1, by have := hw a.1 a.2; have := hb a.1 a.2; omega⟩
  have hw' : w'.map lab = w := by
    simp only [w', List.map_map]
    conv_rhs => rw [← List.attach_map_subtype_val w]
    apply List.map_congr_left
    intro a _
    have := hw a.1 a.2
    simp only [Function.comp_apply, lab]
    omega
  obtain ⟨hex, huniq⟩ := theorem_4_1_insertion n w'
  rw [hw'] at hex huniq
  exact ⟨insertionTableau n w', hex, fun S hS => huniq S hS⟩

/-! ## The plactic monoid and the tableau basis of its monoid algebra -/

/-- Knuth equivalence as a congruence on the free monoid (it is one by `knuth_context`). -/
def knuthCon : Con (FreeMonoid ℕ) where
  r a b := KnuthEquiv (FreeMonoid.toList a) (FreeMonoid.toList b)
  iseqv := ⟨fun _ => knuth_refl _, knuth_symm, knuth_trans⟩
  mul' := by
    intro a b c d h₁ h₂
    have e₁ := knuth_context h₁ [] (FreeMonoid.toList c)
    have e₂ := knuth_context h₂ (FreeMonoid.toList b) []
    simp only [List.nil_append, List.append_nil] at e₁ e₂
    exact knuth_trans e₁ e₂

/-- `knuthCon` is exactly the congruence generated by the printed relations (K′), (K″). -/
theorem knuthCon_eq_conGen :
    knuthCon = conGen (fun a b : FreeMonoid ℕ => KStep (FreeMonoid.toList a) (FreeMonoid.toList b)) := by
  apply le_antisymm
  · intro a b h
    change KnuthEquiv (FreeMonoid.toList a) (FreeMonoid.toList b) at h
    have key : ∀ w w' : List ℕ, KnuthEquiv w w' →
        conGen (fun a b : FreeMonoid ℕ => KStep (FreeMonoid.toList a) (FreeMonoid.toList b))
          (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
      intro w w' hk
      induction hk with
      | rel x y hxy => exact ConGen.Rel.of _ _ hxy
      | refl x => exact (conGen _).refl _
      | symm x y _ ih => exact (conGen _).symm ih
      | trans x y z _ _ ih₁ ih₂ => exact (conGen _).trans ih₁ ih₂
    exact key _ _ h
  · exact Con.conGen_le fun x y h => Relation.EqvGen.rel _ _ h

/-- Positive words: the alphabet `A = ℤ_{>0}` of EK Sec. 4.1. -/
def PosWord (w : List ℕ) : Prop := ∀ a ∈ w, 0 < a

/-- The plactic monoid on `A = ℤ_{>0}`: classes of positive words modulo (K′), (K″)
(with the empty word as unit; the printed non-unital monoid is the complement of `1`). -/
def plSub : Submonoid knuthCon.Quotient where
  carrier := {x | ∃ w : List ℕ, PosWord w ∧ x = ((FreeMonoid.ofList w : FreeMonoid ℕ) : knuthCon.Quotient)}
  one_mem' := ⟨[], by simp [PosWord], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨w₁, h₁, rfl⟩ ⟨w₂, h₂, rfl⟩
    refine ⟨w₁ ++ w₂, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h₁ a ha
      · exact h₂ a ha
    · rw [FreeMonoid.ofList_append, Con.coe_mul]

/-- The plactic monoid `Pl`. -/
abbrev Pl : Type := plSub

/-- The plactic ring `ℤPl` (monoid algebra). -/
abbrev ZPl : Type := MonoidAlgebra ℤ Pl

theorem rowWord_pos {μ : YoungDiagram} (T : PositiveTableau μ) : PosWord (TableauRowWord.rowWord T) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact T.positive (show (p.1, p.2) ∈ μ from (TableauRowWord.mem_rowCells μ p).mp hp)

/-- EK (4.2): `T ↦ wr(T)` into the plactic monoid. -/
noncomputable def tabToPl (S : Σ μ : YoungDiagram, PositiveTableau μ) : Pl :=
  ⟨((FreeMonoid.ofList (TableauRowWord.rowWord S.2) : FreeMonoid ℕ) : knuthCon.Quotient),
    TableauRowWord.rowWord S.2, rowWord_pos S.2, rfl⟩

/-- EK Thm 4.1, monoid form: `T ↦ wr(T)` is a bijection from SSYT onto `Pl`. -/
theorem tabToPl_bijective : Function.Bijective tabToPl := by
  constructor
  · rintro ⟨μ, T⟩ ⟨μ', T'⟩ h
    have h' := congrArg Subtype.val h
    simp only [tabToPl] at h'
    exact tableau_eq_of_knuth T T' (Con.eq knuthCon |>.mp h')
  · rintro ⟨x, w, hw, rfl⟩
    obtain ⟨S, hS, -⟩ := theorem_4_1 w hw
    refine ⟨S, Subtype.ext ?_⟩
    exact (Con.eq knuthCon).mpr (knuth_symm hS)

/-- SSYT ≃ plactic monoid. -/
noncomputable def tabEquivPl : (Σ μ : YoungDiagram, PositiveTableau μ) ≃ Pl :=
  Equiv.ofBijective tabToPl tabToPl_bijective

/-- EK, after Thm 4.1: the semistandard tableaux (via their row words) form a `ℤ`-basis
of the plactic ring `ℤPl`. -/
noncomputable def tableauBasis : Basis (Σ μ : YoungDiagram, PositiveTableau μ) ℤ ZPl :=
  (Finsupp.basisSingleOne : Basis Pl ℤ (Pl →₀ ℤ)).reindex tabEquivPl.symm

theorem tableauBasis_apply (S : Σ μ : YoungDiagram, PositiveTableau μ) :
    tableauBasis S = MonoidAlgebra.of ℤ Pl (tabToPl S) := by
  change ((Finsupp.basisSingleOne : Basis Pl ℤ (Pl →₀ ℤ)).reindex tabEquivPl.symm) S =
    Finsupp.single (tabToPl S) (1 : ℤ)
  rw [Basis.reindex_apply, Equiv.symm_symm, Finsupp.coe_basisSingleOne]
  rfl

/-- Knuth moves preserve length, so the class of the empty word is `{[]}`: the printed
non-unital `Pl` is `Pl¹` minus the unit, and `ℤPl` is spanned by the basis vectors of the
nonempty tableaux (those with nonempty row word). -/
theorem knuth_nil_iff (w : List ℕ) : KnuthEquiv [] w ↔ w = [] := by
  constructor
  · intro h
    exact List.eq_nil_of_length_eq_zero ((perm_of_knuth h).length_eq.symm.trans rfl)
  · rintro rfl
    exact knuth_refl _

theorem tabToPl_eq_one_iff (S : Σ μ : YoungDiagram, PositiveTableau μ) :
    tabToPl S = 1 ↔ TableauRowWord.rowWord S.2 = [] := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    have h2 : knuthCon (FreeMonoid.ofList (TableauRowWord.rowWord S.2))
        (FreeMonoid.ofList ([] : List ℕ)) := Con.eq _ |>.mp h1
    exact (knuth_nil_iff _).mp (knuth_symm h2)
  · intro h
    apply Subtype.ext
    change ((FreeMonoid.ofList (TableauRowWord.rowWord S.2) : FreeMonoid ℕ) : knuthCon.Quotient) =
      ((FreeMonoid.ofList ([] : List ℕ) : FreeMonoid ℕ) : knuthCon.Quotient)
    rw [h]

/-! ## The printed non-unital plactic monoid and ring

EK define `Pl` as the associative monoid *without unit* on `A`. Since Knuth moves preserve
length, the classes of nonempty positive words are exactly the elements `≠ 1` of `Pl` above,
and they are closed under multiplication. This gives the printed semigroup `PlNonunital`, its
(non-unital) monoid algebra `ℤPl`, and the tableau basis indexed by the nonempty SSYT. -/

theorem mk_eq_one_iff (w : List ℕ) (hw : PosWord w) :
    (⟨((FreeMonoid.ofList w : FreeMonoid ℕ) : knuthCon.Quotient), w, hw, rfl⟩ : Pl) = 1 ↔
      w = [] := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    have h2 : knuthCon (FreeMonoid.ofList w) (FreeMonoid.ofList ([] : List ℕ)) :=
      Con.eq _ |>.mp h1
    exact (knuth_nil_iff _).mp (knuth_symm h2)
  · rintro rfl
    apply Subtype.ext
    rfl

/-- The printed plactic monoid without unit: the nonempty classes, closed under product. -/
def PlNonunital : Subsemigroup Pl where
  carrier := {x | x ≠ 1}
  mul_mem' := by
    rintro ⟨_, w₁, h₁, rfl⟩ ⟨_, w₂, h₂, rfl⟩ hx _ hxy
    apply hx
    have e1 := congrArg Subtype.val hxy
    have e2 : knuthCon (FreeMonoid.ofList w₁ * FreeMonoid.ofList w₂)
        (FreeMonoid.ofList ([] : List ℕ)) := Con.eq _ |>.mp e1
    have e3 : KnuthEquiv [] (w₁ ++ w₂) := knuth_symm e2
    have e4 := (knuth_nil_iff _).mp e3
    exact (mk_eq_one_iff w₁ h₁).mpr (List.append_eq_nil_iff.mp e4).1

/-- The printed (non-unital) plactic ring `ℤPl`: the `ℤ`-span of `PlNonunital`. -/
abbrev ZPlNonunital : Type := MonoidAlgebra ℤ PlNonunital

/-- Nonempty SSYT ≃ the printed non-unital plactic monoid, via `T ↦ wr(T)`. -/
noncomputable def tabEquivPlNonunital :
    {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []} ≃
      PlNonunital :=
  tabEquivPl.subtypeEquiv fun S => by
    show TableauRowWord.rowWord S.2 ≠ [] ↔ tabToPl S ≠ 1
    rw [Ne, Ne, tabToPl_eq_one_iff]

theorem tabEquivPlNonunital_apply
    (S : {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []}) :
    ((tabEquivPlNonunital S : PlNonunital) : Pl) = tabToPl S.1 := rfl

/-- EK, after Thm 4.1, for the printed non-unital `ℤPl`: the (nonempty) semistandard
tableaux form a `ℤ`-basis. -/
noncomputable def tableauBasisNonunital :
    Basis {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []} ℤ
      ZPlNonunital :=
  (Finsupp.basisSingleOne : Basis PlNonunital ℤ (PlNonunital →₀ ℤ)).reindex
    tabEquivPlNonunital.symm

theorem tableauBasisNonunital_apply
    (S : {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []}) :
    tableauBasisNonunital S = Finsupp.single (tabEquivPlNonunital S) (1 : ℤ) := by
  change ((Finsupp.basisSingleOne : Basis PlNonunital ℤ (PlNonunital →₀ ℤ)).reindex
    tabEquivPlNonunital.symm) S = _
  rw [Basis.reindex_apply, Equiv.symm_symm, Finsupp.coe_basisSingleOne]

end OddMath.Frontier.EKClassicalPlactic

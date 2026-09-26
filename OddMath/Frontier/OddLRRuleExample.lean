import OddMath.Frontier.OddLRRule

/-!
# Example 4.9 of Ellis, arXiv:1111.3932v1

E Example 4.9, p.15: `c^{(3,2,1)}_{(2,1),(2,1)} = 0` (the even coefficient is `2`). The
Littlewood–Richardson tableaux of shape `(3,2,1)/(2,1)` and content `(2,1)` are the two fillings
of the cells `(1,3), (2,2), (3,1)` (one-based) by `1,1,2` and `1,2,1` (read top to bottom), with
`N^< = 7` and `N^< = 6`.
-/

namespace OddMath.Frontier.OddLRRule

open OddLRTableau TableauSign

/-- `(3,2,1)`. -/
def shape321 : YoungDiagram := YoungDiagram.ofRowLens [3, 2, 1] (by decide)

/-- `(2,1)`. -/
def shape21 : YoungDiagram := YoungDiagram.ofRowLens [2, 1] (by decide)

theorem skewCells_ex : skewCells shape321 shape21 = {(0, 2), (1, 1), (2, 0)} := by decide

theorem bound321 {i j : ℕ} (h : (i, j) ∈ shape321) : i < 3 ∧ j < 3 := by
  rw [shape321, YoungDiagram.mem_ofRowLens] at h
  obtain ⟨hi, hj⟩ := h
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> simp at hj <;> omega

/-- The filling with entries `a, b, c` in the cells `(0,2), (1,1), (2,0)` (zero-based). -/
def exEntry (a b c : ℕ) (i j : ℕ) : ℕ :=
  if (i, j) = (0, 2) then a else if (i, j) = (1, 1) then b else if (i, j) = (2, 0) then c else 0

/-- Every positive filling of `(3,2,1)/(2,1)` is semistandard (no two cells share a row or a
column, and no cell lies weakly south-east of another). -/
def exTab (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : SkewTableau shape321 shape21 where
  entry := exEntry a b c
  sub := YoungDiagram.cells_subset_iff.mp (by decide)
  row_weak := by
    intro i j₁ j₂ hj h h1
    exfalso
    obtain ⟨hi, hj2⟩ := bound321 h
    revert h h1
    interval_cases i <;> interval_cases j₂ <;> interval_cases j₁ <;> decide
  col_strict := by
    intro i₁ i₂ j hi h h1
    exfalso
    obtain ⟨hi2, hj⟩ := bound321 h
    revert h h1
    interval_cases i₂ <;> interval_cases i₁ <;> interval_cases j <;> decide
  zeros_out := by
    intro i j h
    unfold exEntry
    split_ifs with h1 h2 h3
    · exact absurd (h1 ▸ (by decide : ((0, 2) : ℕ × ℕ) ∈ shape321)) h
    · exact absurd (h2 ▸ (by decide : ((1, 1) : ℕ × ℕ) ∈ shape321)) h
    · exact absurd (h3 ▸ (by decide : ((2, 0) : ℕ × ℕ) ∈ shape321)) h
    · rfl
  zeros_in := by
    intro i j h
    unfold exEntry
    split_ifs with h1 h2 h3
    · exact absurd (h1 ▸ h) (by decide)
    · exact absurd (h2 ▸ h) (by decide)
    · exact absurd (h3 ▸ h) (by decide)
    · rfl
  positive := by
    intro i j h h'
    have hs : (i, j) ∈ skewCells shape321 shape21 := mem_skewCells.mpr ⟨h, h'⟩
    rw [skewCells_ex] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    unfold exEntry
    rcases hs with h1 | h1 | h1 <;> simp [h1, ha, hb, hc, Prod.ext_iff]

theorem eq_exTab (S : SkewTableau shape321 shape21) :
    ∃ ha hb hc, S = exTab (S.entry 0 2) (S.entry 1 1) (S.entry 2 0) ha hb hc := by
  have hp : ∀ p ∈ skewCells shape321 shape21, 0 < S.entry p.1 p.2 := fun p hp =>
    S.positive (mem_skewCells.mp hp).1 (mem_skewCells.mp hp).2
  refine ⟨hp (0, 2) (by decide), hp (1, 1) (by decide), hp (2, 0) (by decide), ?_⟩
  apply SkewTableau.ext_skew
  intro p hp'
  rw [skewCells_ex] at hp'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
  rcases hp' with rfl | rfl | rfl <;> simp [exTab, exEntry, Prod.ext_iff]

theorem rowCells_ex : TableauRowWord.rowCells shape321 = [(2, 0), (1, 0), (1, 1), (0, 0), (0, 1), (0, 2)] := by
  apply List.eq_of_perm_of_sorted (r := TableauRowWord.RowLE)
  · apply (List.perm_ext_iff_of_nodup (TableauRowWord.rowCells_nodup _) (by decide)).mpr
    intro p
    rw [TableauRowWord.mem_rowCells]
    constructor
    · intro hp
      have hb := bound321 (show (p.1, p.2) ∈ shape321 from by simpa using hp)
      obtain ⟨i, j⟩ := p
      simp only at hb
      obtain ⟨hi, hj⟩ := hb
      revert hp
      interval_cases i <;> interval_cases j <;> decide
    · intro hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact TableauRowWord.rowCells_sorted _
  · decide

theorem rowWord_exTab (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (exTab a b c ha hb hc).rowWord = [c, b, a] := by
  unfold SkewTableau.rowWord
  rw [rowCells_ex, show List.filter (fun p => decide (p ∉ shape21.cells))
    [(2, 0), (1, 0), (1, 1), (0, 0), (0, 1), (0, 2)] = [(2, 0), (1, 1), (0, 2)] by decide]
  rfl

theorem hatWord_exTab (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (exTab a b c ha hb hc).hatWord = [c, 0, b, 0, 0, a] := by
  unfold SkewTableau.hatWord
  rw [rowCells_ex]
  rfl

theorem content_exTab (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℕ) :
    (exTab a b c ha hb hc).content k =
      (if a = k then 1 else 0) + (if b = k then 1 else 0) + (if c = k then 1 else 0) := by
  rw [SkewTableau.content_apply, skewCells_ex, Finset.card_filter, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [add_assoc]
  rfl

theorem shapeContent21 (k : ℕ) :
    TableauDominance.shapeContent shape21 k = if k = 1 then 2 else if k = 2 then 1 else 0 := by
  rcases k with _ | i
  · simp [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · rw [shapeContent_succ]
    rcases i with _ | _ | i
    · exact YoungDiagram.rowLen_ofRowLens (w := [2, 1]) (hw := by decide) ⟨0, by simp⟩
    · exact YoungDiagram.rowLen_ofRowLens (w := [2, 1]) (hw := by decide) ⟨1, by simp⟩
    · rw [if_neg (by omega), if_neg (by omega)]
      apply rowLen_eq_zero
      have h2 : ((2, 0) : ℕ × ℕ) ∉ shape21 := by decide
      have a2 : ¬ (2 < shape21.colLen 0) := fun h => h2 (YoungDiagram.mem_iff_lt_colLen.mpr h)
      omega

attribute [local instance] Classical.propDecidable

/-- The first LR tableau of E Example 4.9 (entries `1, 1, 2` from top to bottom). -/
def exS1 : SkewTableau shape321 shape21 := exTab 1 1 2 one_pos one_pos two_pos

/-- The second LR tableau of E Example 4.9 (entries `1, 2, 1` from top to bottom). -/
def exS2 : SkewTableau shape321 shape21 := exTab 1 2 1 one_pos two_pos one_pos

theorem good_of_le_two (t : List ℕ) (ht : ∀ x ∈ t, x ≤ 2) (h : t.count 2 ≤ t.count 1) : Good t := by
  intro a ha
  rcases Nat.lt_or_ge a 2 with h1 | h1
  · rw [show a = 1 by omega]; exact h
  · rw [List.count_eq_zero_of_not_mem (fun hm => by have := ht _ hm; omega)]
    exact Nat.zero_le _

theorem yamanouchi_small (w : List ℕ) (hw : ∀ x ∈ w, x ≤ 2)
    (h : ∀ t, t <:+ w → t.count 2 ≤ t.count 1) : Yamanouchi w := by
  rw [yamanouchi_iff_yamR, yamR_iff_suffix]
  intro t ht
  exact good_of_le_two t (fun x hx => hw x (ht.subset hx)) (h t ht)

theorem content_exS (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ({a, b, c} : Multiset ℕ) = {1, 1, 2}) :
    (exTab a b c ha hb hc).content = TableauDominance.shapeContent shape21 := by
  ext k
  rw [content_exTab, shapeContent21]
  have hk := congrArg (fun s : Multiset ℕ => s.count k) h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hk
  split_ifs at hk ⊢ <;> omega

/-- The LR tableaux of shape `(3,2,1)/(2,1)` and content `(2,1)`. -/
theorem lrTableaux_ex : lrTableaux shape321 shape21 shape21 = {exS1, exS2} := by
  ext S
  rw [mem_lrTableaux, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hy⟩
    obtain ⟨ha, hb, hcc, hS⟩ := eq_exTab S
    generalize S.entry 0 2 = a at ha hS
    generalize S.entry 1 1 = b at hb hS
    generalize S.entry 2 0 = c at hcc hS
    subst hS
    have h1 := congrArg (fun f => f 1) hc
    have h2 := congrArg (fun f => f 2) hc
    simp only [content_exTab, shapeContent21] at h1 h2
    unfold IsLR at hy
    rw [rowWord_exTab] at hy
    have hna : a ≠ 2 := by
      intro ha2
      have hb1 : b = 1 := by split_ifs at h1 h2 <;> omega
      have hc1 : c = 1 := by split_ifs at h1 h2 <;> omega
      have := hy [a] (by rw [hb1, hc1]; exact List.suffix_append [1, 1] [a]) 1 2 one_pos one_lt_two
      rw [ha2] at this
      simp at this
    have hcase : (a = 1 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 1) := by
      split_ifs at h1 h2 <;> omega
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · refine ⟨content_exS 1 1 2 _ _ _ (by decide), ?_⟩
      unfold IsLR exS1
      rw [rowWord_exTab]
      apply yamanouchi_small _ (by decide)
      intro t ht
      have := (List.mem_tails t _).mpr ht
      simp only [List.tails, List.mem_cons, List.mem_nil_iff, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> decide
    · refine ⟨content_exS 1 2 1 _ _ _ (by decide), ?_⟩
      unfold IsLR exS2
      rw [rowWord_exTab]
      apply yamanouchi_small _ (by decide)
      intro t ht
      have := (List.mem_tails t _).mpr ht
      simp only [List.tails, List.mem_cons, List.mem_nil_iff, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> decide

theorem Nlt_exS1 : exS1.Nlt = 7 := by
  unfold SkewTableau.Nlt exS1; rw [hatWord_exTab]; decide

theorem Nlt_exS2 : exS2.Nlt = 6 := by
  unfold SkewTableau.Nlt exS2; rw [hatWord_exTab]; decide

/-- **E Example 4.9**: `c^{(3,2,1)}_{(2,1),(2,1)} = 0`. -/
theorem example_4_9 : oddLR shape321 shape21 shape21 = 0 := by
  have hne : exS1 ≠ exS2 := by
    intro h
    have := congrArg (fun S : SkewTableau shape321 shape21 => S.entry 1 1) h
    exact absurd this (by decide)
  rw [thm_4_8, lrSignedCount, lrTableaux_ex, Finset.sum_pair hne]
  unfold SkewTableau.sign
  rw [Nlt_exS1, Nlt_exS2]
  norm_num

end OddMath.Frontier.OddLRRule

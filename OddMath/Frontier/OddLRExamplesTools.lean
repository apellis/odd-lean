import OddMath.Frontier.OddLREvenPieri

/-!
# Explicit tableaux, reading orders and Littlewood–Richardson counts

Tools for checking the worked examples of Ellis, "The odd Littlewood–Richardson rule",
arXiv:1111.3932v1, by kernel computation on the library's own objects:

* `rowCells_ofRowLens`: the reading order (left to right, bottom to top) of the cells of the
  diagram with row lengths `w`, as an explicit list;
* `ofWord`: the skew tableau of shape `λ/μ` with a prescribed row word (checked by `decide`);
* `card_lrTableaux_eq`: the number of Littlewood–Richardson tableaux of shape `λ/μ` and content
  `ν` equals an explicit count over words;
* `partsF`, `rowLens_mem_partsF`: every partition of `n` occurs in an explicit list;
* `posTab`: a semistandard tableau given by its rows.
-/

namespace OddMath.Frontier.OddLRExamples

open scoped BigOperators
open TableauSign TableauContent TableauRowWord OddLRTableau OddLRRule OddLREven

/-! ## The reading order of `ofRowLens w` -/

/-- Cells of the diagram with row lengths `w`, left to right and bottom to top. -/
def rowCellsOf (w : List ℕ) : List (ℕ × ℕ) :=
  (List.range w.length).reverse.flatMap (fun i => (List.range (w.getD i 0)).map (fun j => (i, j)))

theorem mem_rowCellsOf {w : List ℕ} {p : ℕ × ℕ} :
    p ∈ rowCellsOf w ↔ p.1 < w.length ∧ p.2 < w.getD p.1 0 := by
  simp only [rowCellsOf, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨hi, hj⟩
  · intro h; exact ⟨p.1, h.1, p.2, h.2, rfl⟩

theorem rowCellsOf_sorted (w : List ℕ) : (rowCellsOf w).Sorted RowLE := by
  unfold rowCellsOf List.Sorted
  rw [List.pairwise_flatMap, List.pairwise_reverse]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun h => Or.inr ⟨rfl, h.le⟩)
  · refine List.pairwise_lt_range.imp (fun {a b} h x hx y hy => ?_)
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j', -, rfl⟩ := List.mem_map.mp hy
    exact Or.inl h

theorem rowCellsOf_nodup (w : List ℕ) : (rowCellsOf w).Nodup := by
  unfold rowCellsOf
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  rw [List.pairwise_reverse]
  refine List.pairwise_lt_range.imp (fun {a b} h => ?_)
  intro x hx hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j', -, h'⟩ := List.mem_map.mp hy
  simp only [Prod.mk.injEq] at h'
  omega

theorem mem_ofRowLens_iff {w : List ℕ} {hw : w.Sorted (· ≥ ·)} {p : ℕ × ℕ} :
    p ∈ YoungDiagram.ofRowLens w hw ↔ p.1 < w.length ∧ p.2 < w.getD p.1 0 := by
  rw [YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, by rw [List.getD_eq_getElem _ _ h]; exact h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, by rw [List.getD_eq_getElem _ _ h] at h'; exact h'⟩

/-- The reading order of `ofRowLens w` is `rowCellsOf w`. -/
theorem rowCells_ofRowLens (w : List ℕ) (hw : w.Sorted (· ≥ ·)) :
    rowCells (YoungDiagram.ofRowLens w hw) = rowCellsOf w := by
  apply List.eq_of_perm_of_sorted (r := RowLE)
  · apply (List.perm_ext_iff_of_nodup (rowCells_nodup _) (rowCellsOf_nodup w)).mpr
    intro p
    rw [mem_rowCells, mem_rowCellsOf, YoungDiagram.mem_cells, mem_ofRowLens_iff]
  · exact rowCells_sorted _
  · exact rowCellsOf_sorted w

/-! ## Skew tableaux with a prescribed row word -/

/-- The conditions on a word `v` to be the row word of a semistandard skew tableau whose
cells, in reading order, are `L`: positive letters, weakly increasing along rows, strictly
increasing down columns. -/
def ValidW (L : List (ℕ × ℕ)) (v : List ℕ) : Prop :=
  v.length = L.length ∧ (∀ x ∈ v, 0 < x) ∧
  (∀ a < L.length, ∀ b < L.length, (L.getD a (0, 0)).1 = (L.getD b (0, 0)).1 →
    (L.getD a (0, 0)).2 < (L.getD b (0, 0)).2 → v.getD a 0 ≤ v.getD b 0) ∧
  (∀ a < L.length, ∀ b < L.length, (L.getD a (0, 0)).2 = (L.getD b (0, 0)).2 →
    (L.getD a (0, 0)).1 < (L.getD b (0, 0)).1 → v.getD a 0 < v.getD b 0)

instance (L : List (ℕ × ℕ)) (v : List ℕ) : Decidable (ValidW L v) := by
  unfold ValidW; infer_instance

section OfWord

variable {lam mu : YoungDiagram} {L : List (ℕ × ℕ)}

/-- Entry function of the skew tableau with row word `v`. -/
def wordEntry (lam mu : YoungDiagram) (L : List (ℕ × ℕ)) (v : List ℕ) (i j : ℕ) : ℕ :=
  if (i, j) ∈ lam ∧ (i, j) ∉ mu then v.getD (idx L (i, j)) 0 else 0

theorem getD_eq {α : Type*} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d = l[i] :=
  List.getD_eq_getElem _ _ h

theorem skew_mem_L (hL : cellsL lam mu = L) {p : ℕ × ℕ} (h1 : p ∈ lam) (h2 : p ∉ mu) : p ∈ L :=
  hL ▸ mem_cellsL.mpr ⟨h1, h2⟩

theorem L_getD_idx {p : ℕ × ℕ} (hp : p ∈ L) : L.getD (idx L p) (0, 0) = p := by
  rw [getD_eq _ _ _ (idx_lt hp), getElem_idx]

/-- The skew tableau of shape `λ/μ` with row word `v`. -/
def ofWord (lam mu : YoungDiagram) (L : List (ℕ × ℕ)) (hL : cellsL lam mu = L)
    (hsub : mu.cells ⊆ lam.cells) (v : List ℕ) (hv : ValidW L v) : SkewTableau lam mu where
  entry := wordEntry lam mu L v
  sub := YoungDiagram.cells_subset_iff.mp hsub
  row_weak := by
    intro i j₁ j₂ hj h h1
    have h1' : (i, j₁) ∈ lam := lam.up_left_mem le_rfl hj.le h
    have h2' : (i, j₂) ∉ mu := fun hm => h1 (mu.up_left_mem le_rfl hj.le hm)
    have ha := skew_mem_L hL h1' h1
    have hb := skew_mem_L hL h h2'
    have := hv.2.2.1 (idx L (i, j₁)) (idx_lt ha) (idx L (i, j₂)) (idx_lt hb)
      (by rw [L_getD_idx ha, L_getD_idx hb]) (by rw [L_getD_idx ha, L_getD_idx hb]; exact hj)
    simp only [wordEntry, if_pos (And.intro h1' h1), if_pos (And.intro h h2')]
    exact this
  col_strict := by
    intro i₁ i₂ j hi h h1
    have h1' : (i₁, j) ∈ lam := lam.up_left_mem hi.le le_rfl h
    have h2' : (i₂, j) ∉ mu := fun hm => h1 (mu.up_left_mem hi.le le_rfl hm)
    have ha := skew_mem_L hL h1' h1
    have hb := skew_mem_L hL h h2'
    have := hv.2.2.2 (idx L (i₁, j)) (idx_lt ha) (idx L (i₂, j)) (idx_lt hb)
      (by rw [L_getD_idx ha, L_getD_idx hb]) (by rw [L_getD_idx ha, L_getD_idx hb]; exact hi)
    simp only [wordEntry, if_pos (And.intro h1' h1), if_pos (And.intro h h2')]
    exact this
  zeros_out := by intro i j h; simp [wordEntry, h]
  zeros_in := by intro i j h; simp [wordEntry, h]
  positive := by
    intro i j h h'
    have ha := skew_mem_L hL h h'
    simp only [wordEntry, if_pos (And.intro h h')]
    have hl : idx L (i, j) < v.length := by rw [hv.1]; exact idx_lt ha
    rw [getD_eq _ _ _ hl]
    exact hv.2.1 _ (List.getElem_mem hl)

theorem rowWord_ofWord (hL : cellsL lam mu = L) (hsub : mu.cells ⊆ lam.cells) (v : List ℕ)
    (hv : ValidW L v) : (ofWord lam mu L hL hsub v hv).rowWord = v := by
  rw [rowWord_eq_map, hL]
  apply List.ext_getElem
  · rw [List.length_map, hv.1]
  · intro n h1 h2
    rw [List.getElem_map]
    have hm : L[n]'(by simpa using h1) ∈ L := List.getElem_mem _
    have hm' : L[n]'(by simpa using h1) ∈ cellsL lam mu := hL ▸ hm
    obtain ⟨hl, hmu⟩ := mem_cellsL.mp hm'
    change wordEntry lam mu L v _ _ = _
    rw [wordEntry, if_pos ⟨hl, hmu⟩]
    have hn : L.Nodup := hL ▸ cellsL_nodup lam mu
    rw [idx_getElem hn, getD_eq _ _ _ h2]

theorem ext_of_rowWord {S S' : SkewTableau lam mu} (h : S.rowWord = S'.rowWord) : S = S' := by
  rw [rowWord_eq_map, rowWord_eq_map, List.map_inj_left] at h
  apply SkewTableau.ext_skew
  intro p hp
  exact h p (mem_cellsL.mpr (mem_skewCells.mp hp))

/-- The row word of a skew tableau satisfies `ValidW`. -/
theorem validW_rowWord (hL : cellsL lam mu = L) (S : SkewTableau lam mu) : ValidW L S.rowWord := by
  have hlen : S.rowWord.length = L.length := by rw [rowWord_eq_map, List.length_map, hL]
  have hget : ∀ a (ha : a < L.length), S.rowWord.getD a 0 =
      S.entry (L.getD a (0, 0)).1 (L.getD a (0, 0)).2 := by
    intro a ha
    rw [getD_eq _ _ _ (by rw [hlen]; exact ha), getD_eq _ _ _ ha]
    simp only [rowWord_eq_map, List.getElem_map, hL]
  have hmem : ∀ a (ha : a < L.length), L.getD a (0, 0) ∈ lam ∧ L.getD a (0, 0) ∉ mu := by
    intro a ha
    rw [getD_eq _ _ _ ha]
    exact mem_cellsL.mp (hL ▸ List.getElem_mem ha)
  refine ⟨hlen, ?_, ?_, ?_⟩
  · intro x hx
    rw [rowWord_eq_map] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := mem_cellsL.mp hp
    exact S.positive h1 h2
  · intro a ha b hb h1 h2
    rw [hget a ha, hget b hb]
    obtain ⟨hal, ham⟩ := hmem a ha
    obtain ⟨hbl, -⟩ := hmem b hb
    generalize L.getD a (0, 0) = pa at *
    generalize L.getD b (0, 0) = pb at *
    obtain ⟨ia, ja⟩ := pa
    obtain ⟨ib, jb⟩ := pb
    simp only at h1 h2 ⊢
    subst h1
    exact S.row_weak h2 hbl ham
  · intro a ha b hb h1 h2
    rw [hget a ha, hget b hb]
    obtain ⟨hal, ham⟩ := hmem a ha
    obtain ⟨hbl, -⟩ := hmem b hb
    generalize L.getD a (0, 0) = pa at *
    generalize L.getD b (0, 0) = pb at *
    obtain ⟨ia, ja⟩ := pa
    obtain ⟨ib, jb⟩ := pb
    simp only at h1 h2 ⊢
    subst h1
    exact S.col_strict h2 hbl ham

end OfWord

/-! ## Counting Littlewood–Richardson tableaux -/

/-- All words of length `n` in the letters `1, …, B`. -/
def words (B : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range B).flatMap (fun a => (words B n).map (fun v => (a + 1) :: v))

theorem mem_words {B : ℕ} : ∀ {n : ℕ} {v : List ℕ},
    v ∈ words B n ↔ v.length = n ∧ ∀ x ∈ v, 0 < x ∧ x ≤ B
  | 0, v => by
    simp only [words, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | n + 1, v => by
    simp only [words, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨a, ha, u, hu, rfl⟩
      rw [mem_words] at hu
      refine ⟨by simp [hu.1], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact hu.2 x hx
    · rintro ⟨hl, hv⟩
      rcases v with _ | ⟨a, u⟩
      · simp at hl
      · have ha := hv a List.mem_cons_self
        refine ⟨a - 1, by omega, u, ?_, by rw [show a - 1 + 1 = a by omega]⟩
        rw [mem_words]
        exact ⟨by simpa using hl, fun x hx => hv x (List.mem_cons_of_mem _ hx)⟩

theorem words_nodup (B : ℕ) : ∀ n, (words B n).Nodup
  | 0 => List.nodup_singleton _
  | n + 1 => by
    unfold words
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => (words_nodup B n).map (fun u u' h => by simpa using h), ?_⟩
    refine List.pairwise_lt_range.imp (fun {a b} h => ?_)
    intro x hx hy
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u', -, h'⟩ := List.mem_map.mp hy
    simp only [List.cons.injEq] at h'
    omega

/-- The lattice condition with letters at most `B`, recursively over suffixes. -/
def yamB (B : ℕ) : List ℕ → Bool
  | [] => true
  | a :: w => decide (∀ c < B, 0 < c → (a :: w).count (c + 1) ≤ (a :: w).count c) && yamB B w

theorem yamB_iff (B : ℕ) : ∀ (w : List ℕ), (∀ x ∈ w, x ≤ B) → (yamB B w = true ↔ Yamanouchi w)
  | [], _ => by
    simp only [yamB, true_iff]
    rw [yamanouchi_iff_yamR]
    trivial
  | a :: w, hw => by
    rw [yamanouchi_iff_yamR]
    simp only [yamB, Bool.and_eq_true, decide_eq_true_eq]
    rw [yamB_iff B w (fun x hx => hw x (List.mem_cons_of_mem _ hx)), yamanouchi_iff_yamR]
    change _ ↔ Good (a :: w) ∧ YamR w
    apply and_congr_left'
    constructor
    · intro h c hc
      by_cases hcB : c < B
      · exact h c hcB hc
      · rw [List.count_eq_zero_of_not_mem (fun hm => by have := hw _ hm; omega)]
        exact Nat.zero_le _
    · intro h c _ hc
      exact h c hc

/-- The number of Littlewood–Richardson words: row words on the cells `L` with content
`nw` (letters `1, …, B`), semistandard and Yamanouchi. -/
def lrCountL (L : List (ℕ × ℕ)) (B : ℕ) (nw : List ℕ) : ℕ :=
  ((words B L.length).filter (fun v => decide (ValidW L v) &&
    (decide (∀ c < B, v.count (c + 1) = nw.getD c 0) && yamB B v))).length

theorem shapeContent_ofRowLens (nw : List ℕ) (hnw : nw.Sorted (· ≥ ·)) (c : ℕ) :
    TableauDominance.shapeContent (YoungDiagram.ofRowLens nw hnw) (c + 1) = nw.getD c 0 := by
  rw [shapeContent_succ]
  by_cases h : c < nw.length
  · rw [List.getD_eq_getElem _ _ h]
    exact YoungDiagram.rowLen_ofRowLens (w := nw) (hw := hnw) ⟨c, h⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    apply rowLen_eq_zero
    by_contra h'
    push_neg at h'
    have := (mem_ofRowLens_iff (hw := hnw) (p := (c, 0))).mp
      (YoungDiagram.mem_iff_lt_colLen.mpr h')
    exact h this.1

theorem shapeContent_zero' (nu : YoungDiagram) : TableauDominance.shapeContent nu 0 = 0 := by
  simp [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- **Littlewood–Richardson counts by computation**: for `λ/μ` with cells `L` in reading order
and `ν` with row lengths `nw`, `#LR(λ/μ, ν) = lrCountL L ℓ(ν) nw`. -/
theorem card_lrTableaux_eq {lam mu : YoungDiagram} {L : List (ℕ × ℕ)} (hL : cellsL lam mu = L)
    (hsub : mu.cells ⊆ lam.cells) (nw : List ℕ) (hnw : nw.Sorted (· ≥ ·)) :
    (lrTableaux lam mu (YoungDiagram.ofRowLens nw hnw)).card = lrCountL L nw.length nw := by
  set B := nw.length
  set nu := YoungDiagram.ofRowLens nw hnw
  -- contents in terms of row words
  have hcont : ∀ S : SkewTableau lam mu, S.content = TableauDominance.shapeContent nu ↔
      (∀ x ∈ S.rowWord, 0 < x ∧ x ≤ B) ∧ ∀ c < B, S.rowWord.count (c + 1) = nw.getD c 0 := by
    intro S
    constructor
    · intro h
      refine ⟨fun x hx => ⟨?_, ?_⟩, fun c _ => ?_⟩
      · rw [rowWord_eq_map] at hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨h1, h2⟩ := mem_cellsL.mp hp
        exact S.positive h1 h2
      · by_contra hxB
        push_neg at hxB
        have hc := List.count_pos_iff.mpr hx
        rw [← skew_content_eq_count, h, show x = (x - 1) + 1 by omega,
          shapeContent_ofRowLens nw hnw, List.getD_eq_default _ _ (by omega)] at hc
        exact lt_irrefl _ hc
      · rw [← skew_content_eq_count, h, shapeContent_ofRowLens]
    · rintro ⟨hb, hc⟩
      ext c
      rw [skew_content_eq_count]
      rcases c with _ | c
      · rw [shapeContent_zero', List.count_eq_zero_of_not_mem (fun hm => by
          have := (hb 0 hm).1; omega)]
      · rw [shapeContent_ofRowLens]
        by_cases hcB : c < B
        · exact hc c hcB
        · rw [List.getD_eq_default _ _ (by omega), List.count_eq_zero_of_not_mem (fun hm => by
            have := (hb _ hm).2; omega)]
  rw [lrCountL, ← List.toFinset_card_of_nodup ((words_nodup B _).filter _)]
  apply Finset.card_bij (fun S _ => S.rowWord)
  · intro S hS
    obtain ⟨hc, hy⟩ := mem_lrTableaux.mp hS
    obtain ⟨hb, hcount⟩ := (hcont S).mp hc
    have hv := validW_rowWord hL S
    rw [List.mem_toFinset, List.mem_filter, mem_words]
    refine ⟨⟨hv.1, hb⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hv, hcount, (yamB_iff B _ (fun x hx => (hb x hx).2)).mpr hy⟩
  · intro S _ S' _ h
    exact ext_of_rowWord h
  · intro v hv
    rw [List.mem_toFinset, List.mem_filter, mem_words] at hv
    obtain ⟨⟨hl, hb⟩, hv⟩ := hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hvalid, hcount, hy⟩ := hv
    refine ⟨ofWord lam mu L hL hsub v hvalid, ?_, rowWord_ofWord hL hsub v hvalid⟩
    rw [mem_lrTableaux, hcont]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [rowWord_ofWord]; exact hb
    · rw [rowWord_ofWord]; exact hcount
    · unfold IsLR
      rw [rowWord_ofWord]
      exact (yamB_iff B v (fun x hx => (hb x hx).2)).mp hy

/-- `cellsL` of explicit diagrams, for computation. -/
theorem cellsL_ofRowLens (lw : List ℕ) (hlw : lw.Sorted (· ≥ ·)) (mu : YoungDiagram) :
    cellsL (YoungDiagram.ofRowLens lw hlw) mu = (rowCellsOf lw).filter (fun p => p ∉ mu.cells) := by
  rw [cellsL, rowCells_ofRowLens]

/-! ## Enumerating partitions -/

/-- Partitions of `n` with parts at most `m` (fuel `f`), as lists of row lengths. -/
def partsF : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, n => if n = 0 then [[]] else []
  | f + 1, m, n => if n = 0 then [[]] else
      (List.range (min m n)).flatMap (fun a => (partsF f (a + 1) (n - (a + 1))).map ((a + 1) :: ·))

theorem mem_partsF : ∀ (f m n : ℕ) (l : List ℕ), l.Sorted (· ≥ ·) → (∀ x ∈ l, 0 < x ∧ x ≤ m) →
    l.sum = n → n ≤ f → l ∈ partsF f m n
  | f, m, n, [], _, _, hs, _ => by
    simp only [List.sum_nil] at hs
    subst hs
    cases f <;> simp [partsF]
  | 0, m, n, x :: l, _, hp, hs, hf => by
    have := (hp x List.mem_cons_self).1
    simp at hs; omega
  | f + 1, m, n, x :: l, hsort, hp, hs, hf => by
    have hx := hp x List.mem_cons_self
    simp only [List.sum_cons] at hs
    have hn : n ≠ 0 := by omega
    simp only [partsF, if_neg hn, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨x - 1, by omega, l, ?_, by rw [show x - 1 + 1 = x by omega]⟩
    rw [show x - 1 + 1 = x by omega]
    have hsort' := List.sorted_cons.mp hsort
    apply mem_partsF f x (n - x) l hsort'.2
    · intro y hy
      exact ⟨(hp y (List.mem_cons_of_mem _ hy)).1, hsort'.1 y hy⟩
    · omega
    · omega

/-- Every Young diagram with `n` cells has row lengths in `partsF n n n`. -/
theorem rowLens_mem_partsF (lam : YoungDiagram) : lam.rowLens ∈ partsF lam.card lam.card lam.card := by
  apply mem_partsF _ _ _ _ lam.rowLens_sorted
  · intro x hx
    refine ⟨lam.pos_of_mem_rowLens x hx, ?_⟩
    rw [← EKIntegralBases.rowLens_sum]
    exact List.le_sum_of_mem hx
  · exact EKIntegralBases.rowLens_sum lam
  · exact le_rfl

theorem eq_ofRowLens_of_rowLens {lam : YoungDiagram} {w : List ℕ} (h : lam.rowLens = w) :
    ∃ hw : w.Sorted (· ≥ ·), lam = YoungDiagram.ofRowLens w hw := by
  subst h
  exact ⟨lam.rowLens_sorted, YoungDiagram.ofRowLens_to_rowLens_eq_self.symm⟩

/-! ## Tableaux given by their rows -/

/-- Entry function of the tableau with rows `rows`. -/
def rowsEntry (rows : List (List ℕ)) (i j : ℕ) : ℕ := (rows.getD i []).getD j 0

/-- The semistandard tableau with rows `rows` (shape `ofRowLens (rows.map length)`), the
conditions being checked on the bounding box `R × C`. -/
def posTab (rows : List (List ℕ)) (hw : (rows.map List.length).Sorted (· ≥ ·)) (R C : ℕ)
    (hbox : ∀ p ∈ (YoungDiagram.ofRowLens _ hw).cells, p.1 < R ∧ p.2 < C)
    (hrow : ∀ i < R, ∀ j₂ < C, ∀ j₁ < j₂, (i, j₂) ∈ YoungDiagram.ofRowLens _ hw →
      rowsEntry rows i j₁ ≤ rowsEntry rows i j₂)
    (hcol : ∀ i₂ < R, ∀ j < C, ∀ i₁ < i₂, (i₂, j) ∈ YoungDiagram.ofRowLens _ hw →
      rowsEntry rows i₁ j < rowsEntry rows i₂ j)
    (hpos : ∀ i < R, ∀ j < C, (i, j) ∈ YoungDiagram.ofRowLens _ hw → 0 < rowsEntry rows i j) :
    PositiveTableau (YoungDiagram.ofRowLens _ hw) where
  entry := rowsEntry rows
  row_weak' := by
    intro i j₁ j₂ hj h
    have := hbox (i, j₂) (by simpa using h)
    exact hrow i this.1 j₂ this.2 j₁ hj h
  col_strict' := by
    intro i₁ i₂ j hi h
    have := hbox (i₂, j) (by simpa using h)
    exact hcol i₂ this.1 j this.2 i₁ hi h
  zeros' := by
    intro i j h
    rw [mem_ofRowLens_iff] at h
    unfold rowsEntry
    simp only [List.length_map] at h
    by_cases hi : i < rows.length
    · have hlen : (rows.map List.length).getD i 0 = (rows.getD i []).length := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
          List.getD_eq_getElem _ _ hi]
      have : ¬ j < (rows.getD i []).length := fun h' => h ⟨hi, hlen ▸ h'⟩
      rw [List.getD_eq_default _ _ (by omega)]
    · have e : rows.getD i [] = [] := List.getD_eq_default rows [] (by omega)
      rw [e]
      simp
  positive := by
    intro i j h
    have := hbox (i, j) (by simpa using h)
    exact hpos i this.1 j this.2 h

theorem posTab_entry (rows : List (List ℕ)) (hw) (R C) (hbox hrow hcol hpos) (i j : ℕ) :
    (posTab rows hw R C hbox hrow hcol hpos).entry i j = rowsEntry rows i j := rfl

theorem rowWord_posTab (rows : List (List ℕ)) (hw) (R C) (hbox hrow hcol hpos) :
    rowWord (posTab rows hw R C hbox hrow hcol hpos) =
      (rowCellsOf (rows.map List.length)).map (fun p => rowsEntry rows p.1 p.2) := by
  rw [rowWord, rowCells_ofRowLens]
  rfl

end OddMath.Frontier.OddLRExamples

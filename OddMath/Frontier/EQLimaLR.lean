import OddMath.Frontier.EQLimaLimit
import OddMath.Frontier.OddLRRule
import OddMath.Frontier.OddLRExamplesTools

/-!
# Dominance bounds for Littlewood–Richardson tableaux

Input for Ellis–Qi, Proposition A.3 (arXiv:1504.01712v2, Appendix A.1.3): the triangularity of
products of odd Schur functions. With the odd Littlewood–Richardson rule of [E]
(Ellis, arXiv:1111.3932v1, Theorem 4.8, `OddLRRule.thm_4_8`),
`c^λ_{μν} = (-1)^{N(μ)+N(λ)} Σ_{S LR of shape λ/μ, content ν} (-1)^{N^<(S)}`, we prove:

* `entry_le_row`: in a Littlewood–Richardson tableau every entry in row `i` (from `0`) is at most
  `i + 1`;
* `dom_of_mem_lrTableaux`: if `λ/μ` carries an LR tableau of content `ν`, then `λ ⊴ μ + ν`
  (dominance of prefix sums of rows; `μ + ν` adds the rows, `addRows`);
* `lrTableaux_addRows`: `λ = μ + ν` carries exactly one LR tableau of content `ν` (row `i`
  filled with `i + 1`);
* `dom_of_oddLR_ne_zero`, `oddLR_addRows`: `c^λ_{μν} ≠ 0 ⇒ λ ⊴ μ + ν`, and
  `c^{μ+ν}_{μν} = ±1`;
* `oddLR_transpose`: `c^{λᵀ}_{μᵀνᵀ} = ± c^λ_{μν}` (from Ellis–Khovanov's automorphism `ψ₁ψ₂`).
-/

namespace OddMath.Frontier.EQLima

open Finset
open OddLRTableau (SkewTableau skewCells mem_skewCells lrTableaux mem_lrTableaux IsLR Yamanouchi
  oddLR lrSignedCount)

/-! ### Prefix sums and dominance -/

/-- The number of boxes in the first `k` rows. -/
def pre (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ range k, μ.rowLen i

/-- Dominance order: `μ ⊴ ν` iff every prefix sum of rows of `μ` is at most that of `ν`. -/
def Dom (μ ν : YoungDiagram) : Prop := ∀ k, pre μ k ≤ pre ν k

theorem Dom.refl (μ : YoungDiagram) : Dom μ μ := fun _ => le_rfl

theorem Dom.trans {μ ν ρ : YoungDiagram} (h1 : Dom μ ν) (h2 : Dom ν ρ) : Dom μ ρ :=
  fun k => (h1 k).trans (h2 k)

theorem eq_of_pre {μ ν : YoungDiagram} (h : ∀ k, pre μ k = pre ν k) : μ = ν := by
  have hr : ∀ i, μ.rowLen i = ν.rowLen i := by
    intro i
    have := h (i + 1)
    rw [pre, pre, Finset.sum_range_succ, Finset.sum_range_succ, ← pre, ← pre, h i] at this
    omega
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, hr]

theorem Dom.antisymm {μ ν : YoungDiagram} (h1 : Dom μ ν) (h2 : Dom ν μ) : μ = ν :=
  eq_of_pre fun k => le_antisymm (h1 k) (h2 k)

theorem card_filter_row_lt (μ : YoungDiagram) (k : ℕ) :
    (μ.cells.filter (fun p => p.1 < k)).card = pre μ k := by
  induction k with
  | zero => simp [pre]
  | succ k ih =>
    have e : μ.cells.filter (fun p => p.1 < k + 1) =
        μ.cells.filter (fun p => p.1 < k) ∪ μ.row k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union, YoungDiagram.mem_row_iff,
        YoungDiagram.mem_cells]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
        exacts [Or.inl ⟨h1, h⟩, Or.inr ⟨h1, h⟩]
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        exacts [⟨h1, by omega⟩, ⟨h1, by omega⟩]
    rw [e, Finset.card_union_of_disjoint, ih, pre, pre, Finset.sum_range_succ,
      ← YoungDiagram.rowLen_eq_card]
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter] at hp
    rw [YoungDiagram.mem_row_iff] at hp'
    omega

/-! ### Adding rows -/

/-- `μ + ν`: the partition with rows `μ_i + ν_i`. -/
def addRows (μ ν : YoungDiagram) : YoungDiagram where
  cells := ((range (μ.colLen 0 + ν.colLen 0)) ×ˢ (range (μ.rowLen 0 + ν.rowLen 0))).filter
    (fun c => c.2 < μ.rowLen c.1 + ν.rowLen c.1)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨-, ha⟩ := ha
    have h1 := μ.rowLen_anti b.1 a.1 hba.1
    have h2 := ν.rowLen_anti b.1 a.1 hba.1
    have hb : b.2 < μ.rowLen b.1 + ν.rowLen b.1 := by have := hba.2; omega
    refine ⟨⟨?_, ?_⟩, hb⟩
    · by_contra hc
      have hμ : μ.rowLen b.1 = 0 := by
        by_contra hne
        have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
        rw [YoungDiagram.mem_iff_lt_colLen] at this; omega
      have hν : ν.rowLen b.1 = 0 := by
        by_contra hne
        have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
        rw [YoungDiagram.mem_iff_lt_colLen] at this; omega
      omega
    · have := μ.rowLen_anti 0 b.1 (Nat.zero_le _)
      have := ν.rowLen_anti 0 b.1 (Nat.zero_le _)
      omega

theorem mem_addRows (μ ν : YoungDiagram) (c : ℕ × ℕ) :
    c ∈ addRows μ ν ↔ c.2 < μ.rowLen c.1 + ν.rowLen c.1 := by
  change c ∈ (addRows μ ν).cells ↔ _
  simp only [addRows, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · by_contra hc
      have hμ : μ.rowLen c.1 = 0 := by
        by_contra hne
        have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
        rw [YoungDiagram.mem_iff_lt_colLen] at this; omega
      have hν : ν.rowLen c.1 = 0 := by
        by_contra hne
        have := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
        rw [YoungDiagram.mem_iff_lt_colLen] at this; omega
      omega
    · have := μ.rowLen_anti 0 c.1 (Nat.zero_le _)
      have := ν.rowLen_anti 0 c.1 (Nat.zero_le _)
      omega

theorem rowLen_addRows (μ ν : YoungDiagram) (i : ℕ) :
    (addRows μ ν).rowLen i = μ.rowLen i + ν.rowLen i := by
  apply rowLen_eq_of
  intro j
  rw [mem_addRows]

theorem pre_addRows (μ ν : YoungDiagram) (k : ℕ) : pre (addRows μ ν) k = pre μ k + pre ν k := by
  simp only [pre, rowLen_addRows, Finset.sum_add_distrib]

theorem addRows_comm (μ ν : YoungDiagram) : addRows μ ν = addRows ν μ :=
  eq_of_pre fun k => by rw [pre_addRows, pre_addRows, add_comm]

theorem le_addRows (μ ν : YoungDiagram) : μ ≤ addRows μ ν := by
  intro c hc
  rw [mem_addRows]
  have := YoungDiagram.mem_iff_lt_rowLen.mp (show (c.1, c.2) ∈ μ from hc)
  omega

theorem Dom.addRows_left {β β' : YoungDiagram} (γ : YoungDiagram) (h : Dom β β') :
    Dom (addRows γ β) (addRows γ β') := fun k => by
  rw [pre_addRows, pre_addRows]; have := h k; omega

theorem addRows_left_cancel {γ β β' : YoungDiagram} (h : addRows γ β = addRows γ β') : β = β' :=
  eq_of_pre fun k => by
    have := congrArg (fun x => pre x k) h
    simp only [pre_addRows] at this
    omega

/-! ### Littlewood–Richardson tableaux -/

section LR

variable {lam mu nu : YoungDiagram}

theorem suffix_of_mem_cellsL {x : ℕ × ℕ} (hx : x ∈ OddLREven.cellsL lam mu) :
    ∃ post : List (ℕ × ℕ), (x :: post) <:+ OddLREven.cellsL lam mu ∧
      ∀ q ∈ post, TableauRowWord.RowLE x q ∧ q ≠ x := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hx
  refine ⟨post, ⟨pre, hsplit.symm⟩, fun q hq => ?_⟩
  have hs := OddLREven.cellsL_sorted lam mu
  have hn := OddLREven.cellsL_nodup lam mu
  rw [hsplit] at hs hn
  rw [List.pairwise_append] at hs
  have h1 := hs.2.1
  rw [List.pairwise_cons] at h1
  refine ⟨h1.1 q hq, fun hqx => ?_⟩
  rw [List.nodup_append] at hn
  have := (List.nodup_cons.mp hn.2.1).1
  exact this (hqx ▸ hq)

/-- In a Littlewood–Richardson tableau, every entry in row `i` is at most `i + 1`. -/
theorem entry_le_row (S : SkewTableau lam mu) (hS : IsLR S) :
    ∀ v i j, (i, j) ∈ lam → (i, j) ∉ mu → S.entry i j = v → v ≤ i + 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro i j hl hm hv
  rcases Nat.lt_or_ge v 2 with hv2 | hv2
  · omega
  have hx : (i, j) ∈ OddLREven.cellsL lam mu := OddLREven.mem_cellsL.mpr ⟨hl, hm⟩
  obtain ⟨post, hsuf, hpost⟩ := suffix_of_mem_cellsL hx
  have hsuf' : ((i, j) :: post).map (fun p => S.entry p.1 p.2) <:+ S.rowWord := by
    rw [OddLREven.rowWord_eq_map]
    exact hsuf.map _
  have hy := hS _ hsuf' (v - 1) v (by omega) (by omega)
  have hcv : 0 < (((i, j) :: post).map (fun p => S.entry p.1 p.2)).count v := by
    rw [List.count_pos_iff]
    exact List.mem_map.mpr ⟨(i, j), List.mem_cons_self, hv⟩
  have hc1 : 0 < (((i, j) :: post).map (fun p => S.entry p.1 p.2)).count (v - 1) := by omega
  rw [List.count_pos_iff, List.mem_map] at hc1
  obtain ⟨q, hq, hqv⟩ := hc1
  rcases List.mem_cons.mp hq with rfl | hq
  · simp only at hqv; omega
  obtain ⟨hrow, hne⟩ := hpost q hq
  have hqL : q ∈ OddLREven.cellsL lam mu := hsuf.subset (List.mem_cons_of_mem _ hq)
  obtain ⟨hql, hqm⟩ := OddLREven.mem_cellsL.mp hqL
  rcases hrow with hlt | ⟨heq, hle⟩
  · have := ih (v - 1) (by omega) q.1 q.2 hql hqm hqv
    simp only at hlt
    omega
  · exfalso
    simp only at heq hle
    have hj : j < q.2 := by
      rcases Nat.lt_or_ge j q.2 with h | h
      · exact h
      · exact absurd (Prod.ext heq.symm (by simp only; omega)) hne
    have := S.row_weak (i := i) hj (by rw [heq]; exact hql) hm
    rw [hv, heq] at this
    have hq' : S.entry q.1 q.2 = v - 1 := hqv
    rw [hq'] at this
    omega

theorem card_skew_row_lt (hle : mu ≤ lam) (k : ℕ) :
    ((skewCells lam mu).filter (fun p => p.1 < k)).card = pre lam k - pre mu k := by
  have e : (skewCells lam mu).filter (fun p => p.1 < k) =
      lam.cells.filter (fun p => p.1 < k) \ mu.cells.filter (fun p => p.1 < k) := by
    ext p
    simp only [OddLRTableau.skewCells, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [e, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _
    (YoungDiagram.cells_subset_iff.mpr hle)), card_filter_row_lt, card_filter_row_lt]

theorem pre_mono (hle : mu ≤ lam) (k : ℕ) : pre mu k ≤ pre lam k := by
  rw [← card_filter_row_lt, ← card_filter_row_lt]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (YoungDiagram.cells_subset_iff.mpr hle))

theorem card_skew_entry_le (S : SkewTableau lam mu)
    (hS : S.content = TableauDominance.shapeContent nu) (k : ℕ) :
    ((skewCells lam mu).filter (fun p => S.entry p.1 p.2 ≤ k)).card = pre nu k := by
  induction k with
  | zero =>
    rw [pre, Finset.sum_range_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    obtain ⟨h1, h2⟩ := mem_skewCells.mp hp
    have := S.positive h1 h2
    omega
  | succ k ih =>
    have e : (skewCells lam mu).filter (fun p => S.entry p.1 p.2 ≤ k + 1) =
        (skewCells lam mu).filter (fun p => S.entry p.1 p.2 ≤ k) ∪
          (skewCells lam mu).filter (fun p => S.entry p.1 p.2 = k + 1) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h2) with h | h
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨h1, h⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        exacts [⟨h1, by omega⟩, ⟨h1, by omega⟩]
    rw [e, Finset.card_union_of_disjoint, ih, ← SkewTableau.content_apply, hS,
      OddLRRule.shapeContent_succ, pre, pre, Finset.sum_range_succ]
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter] at hp hp'
    omega

/-- **Dominance bound**: if `λ/μ` carries a Littlewood–Richardson tableau of content `ν`, then
`λ ⊴ μ + ν`. -/
theorem dom_of_mem_lrTableaux {S : SkewTableau lam mu} (hS : S ∈ lrTableaux lam mu nu) :
    Dom lam (addRows mu nu) := by
  obtain ⟨hc, hlr⟩ := mem_lrTableaux.mp hS
  intro k
  have hsub : (skewCells lam mu).filter (fun p => p.1 < k) ⊆
      (skewCells lam mu).filter (fun p => S.entry p.1 p.2 ≤ k) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨h1, h2⟩ := mem_skewCells.mp hp.1
    have := entry_le_row S hlr _ p.1 p.2 h1 h2 rfl
    exact ⟨hp.1, by omega⟩
  have h1 := Finset.card_le_card hsub
  rw [card_skew_row_lt S.sub, card_skew_entry_le S hc] at h1
  have h2 := pre_mono S.sub k
  rw [pre_addRows]
  omega

/-- In `λ = μ + ν`, every Littlewood–Richardson tableau of content `ν` has row `i` filled
with `i + 1`. -/
theorem entry_of_mem_lrTableaux_addRows {S : SkewTableau (addRows mu nu) mu}
    (hS : S ∈ lrTableaux (addRows mu nu) mu nu) {i j : ℕ} (h1 : (i, j) ∈ addRows mu nu)
    (h2 : (i, j) ∉ mu) : S.entry i j = i + 1 := by
  obtain ⟨hc, hlr⟩ := mem_lrTableaux.mp hS
  have hle := entry_le_row S hlr _ i j h1 h2 rfl
  set k := S.entry i j with hk
  have hsub : (skewCells (addRows mu nu) mu).filter (fun p => p.1 < k) ⊆
      (skewCells (addRows mu nu) mu).filter (fun p => S.entry p.1 p.2 ≤ k) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨h1, h2⟩ := mem_skewCells.mp hp.1
    have := entry_le_row S hlr _ p.1 p.2 h1 h2 rfl
    exact ⟨hp.1, by omega⟩
  have hcard : ((skewCells (addRows mu nu) mu).filter (fun p => p.1 < k)).card =
      ((skewCells (addRows mu nu) mu).filter (fun p => S.entry p.1 p.2 ≤ k)).card := by
    rw [card_skew_row_lt S.sub, card_skew_entry_le S hc, pre_addRows]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hmem : (i, j) ∈ (skewCells (addRows mu nu) mu).filter (fun p => S.entry p.1 p.2 ≤ k) :=
    Finset.mem_filter.mpr ⟨mem_skewCells.mpr ⟨h1, h2⟩, le_rfl⟩
  rw [← heq, Finset.mem_filter] at hmem
  simp only at hmem
  omega

/-! ### The canonical Littlewood–Richardson tableau of `(μ + ν)/μ` -/

/-- Row `i` of `(μ + ν)/μ` filled with `i + 1`. -/
noncomputable def canonSkew (mu nu : YoungDiagram) : SkewTableau (addRows mu nu) mu where
  entry i j := by
    classical
    exact if (i, j) ∈ addRows mu nu ∧ (i, j) ∉ mu then i + 1 else 0
  sub := le_addRows mu nu
  row_weak := by
    intro i j₁ j₂ hj h h1
    have h1' : (i, j₁) ∈ addRows mu nu := (addRows mu nu).up_left_mem le_rfl hj.le h
    have h2' : (i, j₂) ∉ mu := fun hm => h1 (mu.up_left_mem le_rfl hj.le hm)
    simp only [h1', h1, h, h2', not_false_eq_true, and_self, ↓reduceIte, le_refl]
  col_strict := by
    intro i₁ i₂ j hi h h1
    have h1' : (i₁, j) ∈ addRows mu nu := (addRows mu nu).up_left_mem hi.le le_rfl h
    have h2' : (i₂, j) ∉ mu := fun hm => h1 (mu.up_left_mem hi.le le_rfl hm)
    simp only [h1', h1, h, h2', not_false_eq_true, and_self, ↓reduceIte]
    omega
  zeros_out := by intro i j h; simp [h]
  zeros_in := by intro i j h; simp [h]
  positive := by intro i j h h'; simp [h, h']

theorem canonSkew_entry {i j : ℕ} (h1 : (i, j) ∈ addRows mu nu) (h2 : (i, j) ∉ mu) :
    (canonSkew mu nu).entry i j = i + 1 := by
  simp [canonSkew, h1, h2]

theorem canonSkew_content :
    (canonSkew mu nu).content = TableauDominance.shapeContent nu := by
  ext v
  rw [SkewTableau.content_apply]
  rcases v with _ | r
  · rw [OddLRExamples.shapeContent_zero', Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    obtain ⟨h1, h2⟩ := mem_skewCells.mp hp
    have := (canonSkew mu nu).positive h1 h2
    omega
  · rw [OddLRRule.shapeContent_succ]
    have e : (skewCells (addRows mu nu) mu).filter
        (fun p => (canonSkew mu nu).entry p.1 p.2 = r + 1) =
        (skewCells (addRows mu nu) mu).filter (fun p => p.1 < r + 1) \
          (skewCells (addRows mu nu) mu).filter (fun p => p.1 < r) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hp, he⟩
        obtain ⟨h1, h2⟩ := mem_skewCells.mp hp
        rw [canonSkew_entry h1 h2] at he
        exact ⟨⟨hp, by omega⟩, fun h => by omega⟩
      · rintro ⟨⟨hp, h1⟩, h2⟩
        obtain ⟨h1', h2'⟩ := mem_skewCells.mp hp
        refine ⟨hp, ?_⟩
        rw [canonSkew_entry h1' h2']
        have : ¬ p.1 < r := fun h => h2 ⟨hp, h⟩
        omega
    have hsub : (skewCells (addRows mu nu) mu).filter (fun p => p.1 < r) ⊆
        (skewCells (addRows mu nu) mu).filter (fun p => p.1 < r + 1) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, by omega⟩
    rw [e, Finset.card_sdiff_of_subset hsub, card_skew_row_lt (le_addRows mu nu),
      card_skew_row_lt (le_addRows mu nu), pre_addRows, pre_addRows]
    simp only [pre, Finset.sum_range_succ]
    omega

theorem rowCells_eq (lam : YoungDiagram) :
    TableauRowWord.rowCells lam = (List.range (lam.colLen 0)).reverse.flatMap
      (fun i => (List.range (lam.rowLen i)).map (fun j => (i, j))) := by
  conv_lhs => rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := lam)]
  rw [OddLRExamples.rowCells_ofRowLens lam.rowLens lam.rowLens_sorted.pairwise,
    OddLRExamples.rowCellsOf, YoungDiagram.length_rowLens]
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_reverse, List.mem_range] at hi
  rw [List.getD_eq_getElem _ _ (by rw [YoungDiagram.length_rowLens]; exact hi),
    YoungDiagram.get_rowLens]

theorem row_filter_map (i : ℕ) :
    (((List.range ((addRows mu nu).rowLen i)).map (fun j => (i, j))).filter
        (fun p => decide (p ∉ mu.cells))).map
      (fun p => (canonSkew mu nu).entry p.1 p.2) = List.replicate (nu.rowLen i) (i + 1) := by
  rw [rowLen_addRows, List.range_add, List.map_append, List.filter_append]
  have hnil : ((List.range (mu.rowLen i)).map (fun j => (i, j))).filter
      (fun p => decide (p ∉ mu.cells)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hj
    simp only [YoungDiagram.mem_cells, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_not]
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  rw [hnil, List.nil_append, List.eq_replicate_iff]
  constructor
  · rw [List.length_map, List.filter_eq_self.mpr, List.length_map, List.length_map,
      List.length_range]
    intro p hp
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    simp only [YoungDiagram.mem_cells, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
    rw [YoungDiagram.mem_iff_lt_rowLen]
    omega
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hp1
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
    rw [List.mem_range] at hj
    have hm : (i, mu.rowLen i + j) ∉ mu := by
      rw [YoungDiagram.mem_iff_lt_rowLen]; omega
    have hl : (i, mu.rowLen i + j) ∈ addRows mu nu := by
      rw [mem_addRows]; simp only; omega
    exact canonSkew_entry hl hm

theorem canonSkew_rowWord :
    (canonSkew mu nu).rowWord =
      EKClassicalPlactic.readR (OddLRRule.canonRows nu.rowLen ((addRows mu nu).colLen 0)) := by
  rw [OddLREven.rowWord_eq_map, OddLREven.cellsL, rowCells_eq, List.filter_flatMap,
    List.map_flatMap]
  rw [EKClassicalPlactic.readR, OddLRRule.canonRows, ← List.map_reverse, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i _
  exact row_filter_map i

theorem canonSkew_isLR : IsLR (canonSkew mu nu) := by
  unfold IsLR
  rw [canonSkew_rowWord, OddLRRule.yamanouchi_iff_yamR]
  exact OddLRRule.yamR_canonRows _ (fun a b h => nu.rowLen_anti a b h) _

theorem canonSkew_mem : canonSkew mu nu ∈ lrTableaux (addRows mu nu) mu nu :=
  mem_lrTableaux.mpr ⟨canonSkew_content, canonSkew_isLR⟩

/-- `(μ + ν)/μ` carries exactly one Littlewood–Richardson tableau of content `ν`. -/
theorem lrTableaux_addRows : lrTableaux (addRows mu nu) mu nu = {canonSkew mu nu} := by
  ext S
  rw [Finset.mem_singleton]
  constructor
  · intro hS
    apply SkewTableau.ext_skew
    intro p hp
    obtain ⟨h1, h2⟩ := mem_skewCells.mp hp
    rw [entry_of_mem_lrTableaux_addRows hS h1 h2, canonSkew_entry h1 h2]
  · rintro rfl
    exact canonSkew_mem

end LR

/-! ### Consequences for the odd Littlewood–Richardson coefficients -/

/-- If `c^λ_{μν} ≠ 0` then `λ ⊴ μ + ν`. -/
theorem dom_of_oddLR_ne_zero {lam mu nu : YoungDiagram} (h : oddLR lam mu nu ≠ 0) :
    Dom lam (addRows mu nu) := by
  rw [OddLRRule.thm_4_8, lrSignedCount] at h
  obtain ⟨S, hS⟩ : (lrTableaux lam mu nu).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, mul_zero] at h
    exact h rfl
  exact dom_of_mem_lrTableaux hS

/-- `c^{μ+ν}_{μν} = ±1`. -/
theorem oddLR_addRows (mu nu : YoungDiagram) :
    oddLR (addRows mu nu) mu nu = 1 ∨ oddLR (addRows mu nu) mu nu = -1 := by
  rw [OddLRRule.thm_4_8, lrSignedCount, lrTableaux_addRows, Finset.sum_singleton,
    SkewTableau.sign, ← pow_add]
  exact neg_one_pow_eq_or ℤ _

/-! ### Transposition -/

open OddLREKIdentification (sK)
open OddGrassmannSchur (sBasis)

theorem repr_psi12 (x : EKRadicalQuotient.Q) (lam : YoungDiagram) :
    sBasis.repr (EKAutomorphisms.psi12 x) lam.transpose =
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card) * sBasis.repr x lam := by
  classical
  have key : (Finsupp.lapply lam.transpose ∘ₗ sBasis.repr.toLinearMap ∘ₗ
      (EKAutomorphisms.psi12 : EKRadicalQuotient.Q →+* EKRadicalQuotient.Q).toAddMonoidHom.toIntLinearMap) =
      ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card)) •
        (Finsupp.lapply lam ∘ₗ sBasis.repr.toLinearMap) := by
    refine sBasis.ext fun κ => ?_
    change sBasis.repr (EKAutomorphisms.psi12 (sBasis κ)) lam.transpose =
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card) * sBasis.repr (sBasis κ) lam
    rw [OddGrassmannSchur.sBasis_apply, OddGrassmannSchur.psi12_sK, map_zsmul,
      Finsupp.smul_apply, smul_eq_mul, ← OddGrassmannSchur.sBasis_apply,
      ← OddGrassmannSchur.sBasis_apply, Module.Basis.repr_self, Module.Basis.repr_self,
      Finsupp.single_apply, Finsupp.single_apply]
    by_cases hκ : κ = lam
    · subst hκ; simp
    · have : κ.transpose ≠ lam.transpose := fun h => hκ (YoungDiagram.transpose_eq_iff.mp h)
      simp [hκ, this]
  exact LinearMap.congr_fun key x

/-- `c^{λᵀ}_{μᵀνᵀ} = ± c^λ_{μν}`, with the sign `ε_λ ε_μ ε_ν`, `ε_κ = (-1)^{ℓ(κ)+|κ|}` in the
notation of `psi12_sK`. -/
theorem oddLR_transpose (lam mu nu : YoungDiagram) :
    (-1 : ℤ) ^ (EKSemiorthogonality.ell mu + mu.card) *
        (-1 : ℤ) ^ (EKSemiorthogonality.ell nu + nu.card) *
        oddLR lam.transpose mu.transpose nu.transpose =
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card) * oddLR lam mu nu := by
  have h := repr_psi12 (sK mu * sK nu) lam
  rw [map_mul, OddGrassmannSchur.psi12_sK, OddGrassmannSchur.psi12_sK, smul_mul_smul_comm,
    map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
  unfold oddLR
  rw [← h]

theorem oddLR_transpose_ne_zero {lam mu nu : YoungDiagram} (h : oddLR lam mu nu ≠ 0) :
    oddLR lam.transpose mu.transpose nu.transpose ≠ 0 := by
  intro h0
  have := oddLR_transpose lam mu nu
  rw [h0, mul_zero, eq_comm] at this
  rcases neg_one_pow_eq_or ℤ (EKSemiorthogonality.ell lam + lam.card) with he | he <;>
    rw [he] at this <;> simp at this <;> exact h this

theorem oddLR_transpose_unit {lam mu nu : YoungDiagram}
    (h : oddLR lam mu nu = 1 ∨ oddLR lam mu nu = -1) :
    oddLR lam.transpose mu.transpose nu.transpose = 1 ∨
      oddLR lam.transpose mu.transpose nu.transpose = -1 := by
  have := oddLR_transpose lam mu nu
  rcases neg_one_pow_eq_or ℤ (EKSemiorthogonality.ell mu + mu.card) with h1 | h1 <;>
  rcases neg_one_pow_eq_or ℤ (EKSemiorthogonality.ell nu + nu.card) with h2 | h2 <;>
  rcases neg_one_pow_eq_or ℤ (EKSemiorthogonality.ell lam + lam.card) with h3 | h3 <;>
  rcases h with h | h <;>
  rw [h1, h2, h3, h] at this <;> omega

end OddMath.Frontier.EQLima

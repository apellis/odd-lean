import OddMath.Frontier.OddLRHive
import OddMath.Frontier.OddLRTableau
import OddMath.Frontier.EKKostkaValues
import OddMath.Frontier.OddLRMiscRemark

/-!
# LR tableaux and LR triangles

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.3, pp. 16–19.

* (4.11) (p. 16): `AS n S`, the triangle of an LR tableau `S` of shape `λ/μ`:
  `a_{0,0} = 0`, `a_{0,j} = μ_j`, `a_{i,j} = #{entries i in row j}` (`coord_AS`).
* Lemma 4.12 (p. 16), with Definition 4.11 (3) corrected: `S ↦ A_S` is a bijection from the LR
  tableaux of shape `λ/μ` and content `ν` onto the integer points of `△_LR(λ, μ, ν)`
  (`lemma_4_12`), for `λ, μ, ν` with at most `n` parts.
* p. 17: `N^<(S) = Q_△(A_S)` (`Nlt_eq_Qtri`); (4.19) (p. 19): `= Q_𝔥(Φ(A_S))` (`Nlt_eq_QH`).
* (4.14) (p. 17) and (4.20) (p. 19): the right side of Theorem 4.8 equals the triangle and
  hive sums (`lrSignedCount_eq_triangles`, `lrSignedCount_eq_hives`); with Theorem 4.8 these
  are (4.14) and (4.20) (`eq_4_14_of_thm_4_8`, `eq_4_20_of_thm_4_8`).
* The printed Definition 4.11 (3) gives `1` on the right of (4.14) for `λ = (2,2)`, `μ = (2)`,
  `ν = (1,1)`, `n = 2`, but `c^{(2,2)}_{(2),(1,1)} = 0` (`printed_4_14_fails`); the printed
  Lemma 4.12 fails for the same data (`printed_lemma_4_12_fails`).
-/

namespace OddMath.Frontier.OddLRHive

open scoped BigOperators
open Finset OddLRTableau TableauRowWord

/-! ## Lists sorted in reading order -/

section lists
variable {α : Type*}

theorem filter_isSuffix (R : α → α → Prop) (P : α → Prop) [DecidablePred P] :
    ∀ (L : List α), L.Pairwise R → (∀ a b, R a b → P a → P b) → L.filter P <:+ L
  | [], _, _ => List.suffix_refl _
  | a :: t, hL, hP => by
    rw [List.pairwise_cons] at hL
    by_cases ha : P a
    · have ht : t.filter P = t := List.filter_eq_self.mpr fun q hq =>
        decide_eq_true (hP a q (hL.1 q hq) ha)
      rw [List.filter_cons_of_pos (by simpa using ha), ht]
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      exact (filter_isSuffix R P t hL.2 hP).trans (List.suffix_cons a t)

theorem drop_eq_filter (R : α → α → Prop) [DecidableRel R]
    (hanti : ∀ a b, R a b → R b a → a = b) (hrefl : ∀ a, R a a) :
    ∀ (L : List α) (k : ℕ) (hk : k < L.length), L.Pairwise R → L.Nodup →
      L.drop k = L.filter (fun q => R (L.get ⟨k, hk⟩) q)
  | [], _, hk, _, _ => absurd hk (by simp)
  | a :: t, 0, _, hL, _ => by
    rw [List.pairwise_cons] at hL
    simp only [List.drop_zero, List.get_eq_getElem, List.getElem_cons_zero]
    rw [List.filter_cons_of_pos (by simpa using hrefl a)]
    rw [List.filter_eq_self.mpr fun q hq => decide_eq_true (hL.1 q hq)]
  | a :: t, k+1, hk, hL, hN => by
    rw [List.pairwise_cons] at hL
    rw [List.nodup_cons] at hN
    simp only [List.drop_succ_cons, List.get_eq_getElem, List.getElem_cons_succ]
    have hk' : k < t.length := by simpa using hk
    have hna : ¬ R t[k] a := fun h =>
      hN.1 (hanti _ _ h (hL.1 _ (List.getElem_mem hk')) ▸ List.getElem_mem hk')
    rw [List.filter_cons_of_neg (by simpa using hna)]
    have := drop_eq_filter R hanti hrefl t k hk' hL.2 hN.2
    simpa using this

/-- Inversions of `L.map f` for a strictly sorted list `L`, as a pair count. -/
theorem inversions_map [DecidableEq α] (lt : α → α → Prop) [DecidableRel lt]
    (hasymm : ∀ a b, lt a b → ¬ lt b a) (f : α → ℕ) :
    ∀ (L : List α), L.Pairwise lt → L.Nodup →
      inversions (L.map f) = ∑ p ∈ L.toFinset, (L.toFinset.filter (fun q => lt p q ∧ f q < f p)).card
  | [], _, _ => by simp [inversions]
  | a :: t, hL, hN => by
    rw [List.pairwise_cons] at hL
    rw [List.nodup_cons] at hN
    have hirr : ¬ lt a a := fun h => hasymm a a h h
    rw [List.map_cons, inversions, inversions_map lt hasymm f t hL.2 hN.2, List.toFinset_cons,
      Finset.sum_insert (by simpa using hN.1)]
    congr 1
    · rw [Finset.filter_insert, if_neg (by simp [hirr])]
      rw [List.filter_map, List.length_map]
      rw [← List.toFinset_card_of_nodup (hN.2.filter _), List.toFinset_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter, List.mem_toFinset, Function.comp, decide_eq_true_eq]
      constructor
      · rintro ⟨hq, h⟩; exact ⟨hq, hL.1 q hq, h⟩
      · rintro ⟨hq, -, h⟩; exact ⟨hq, h⟩
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.filter_insert, if_neg]
      rintro ⟨h, -⟩
      exact hasymm a p (hL.1 p (List.mem_toFinset.mp hp)) h

end lists

/-! ## Sums over the cells of a diagram, row by row -/

theorem sum_cells_rows {M : Type*} [AddCommMonoid M] (lam : YoungDiagram) (F : ℕ × ℕ → M) :
    ∑ p ∈ lam.cells, F p =
      ∑ r ∈ range (lam.colLen 0), ∑ c ∈ range (lam.rowLen r), F (r, c) := by
  classical
  rw [← EKKostkaValues.cells_box, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext c
  simp only [mem_filter, mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨lam.up_left_mem (Nat.zero_le _) le_rfl h, h⟩

theorem rowLen_eq_zero_of_le {lam : YoungDiagram} {r : ℕ} (h : lam.colLen 0 ≤ r) :
    lam.rowLen r = 0 := by
  by_contra hne
  have : (r, 0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
  have := YoungDiagram.mem_iff_lt_colLen.mp this
  omega

theorem sum_cells_rows_n {M : Type*} [AddCommMonoid M] (lam : YoungDiagram) {n : ℕ}
    (hl : lam.colLen 0 ≤ n) (F : ℕ × ℕ → M) :
    ∑ p ∈ lam.cells, F p = ∑ r ∈ range n, ∑ c ∈ range (lam.rowLen r), F (r, c) := by
  rw [sum_cells_rows]
  apply Finset.sum_subset
  · intro r hr
    simp only [mem_range] at hr ⊢
    omega
  · intro r _ hr
    simp only [mem_range, not_lt] at hr
    rw [rowLen_eq_zero_of_le hr, Finset.sum_range_zero]

theorem shapeContent_apply (nu : YoungDiagram) (k : ℕ) :
    TableauDominance.shapeContent nu (k+1) = nu.rowLen k := by
  classical
  simp only [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_boole, Nat.cast_id, YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  congr 1
  ext p
  simp only [mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_row_iff, add_left_inj]

theorem shapeContent_zero (nu : YoungDiagram) : TableauDominance.shapeContent nu 0 = 0 := by
  classical
  simp only [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  exact Finset.sum_eq_zero fun p _ => if_neg (by omega)

/-! ## Rows of a skew tableau -/

theorem initial_segment (m : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ c₁ c₂, c₁ ≤ c₂ → c₂ < m → P c₂ → P c₁) {c : ℕ} (hc : c < m) :
    P c ↔ c < ((range m).filter P).card := by
  constructor
  · intro h
    have hsub : range (c+1) ⊆ (range m).filter P := by
      intro d hd
      simp only [mem_range, mem_filter] at hd ⊢
      exact ⟨by omega, hP d c (by omega) hc h⟩
    have := card_le_card hsub
    rw [card_range] at this
    omega
  · intro h
    by_contra hn
    have hsub : (range m).filter P ⊆ range c := by
      intro d hd
      simp only [mem_range, mem_filter] at hd ⊢
      by_contra hdc
      exact hn (hP c d (by omega) hd.1 hd.2)
    have := card_le_card hsub
    rw [card_range] at this
    omega

section tableau
variable {lam mu : YoungDiagram}

theorem mem_of_le (h : mu ≤ lam) {p : ℕ × ℕ} (hp : p ∈ mu) : p ∈ lam := by
  have := YoungDiagram.cells_subset_iff.mpr h
  simpa using this (by simpa using hp)

theorem rowLen_le_of_le (h : mu ≤ lam) (r : ℕ) : mu.rowLen r ≤ lam.rowLen r := by
  by_contra hc
  push_neg at hc
  have := YoungDiagram.mem_iff_lt_rowLen.mp
    (mem_of_le h (YoungDiagram.mem_iff_lt_rowLen.mpr hc : (r, lam.rowLen r) ∈ mu))
  omega

theorem colLen_le_of_le (h : mu ≤ lam) : mu.colLen 0 ≤ lam.colLen 0 := by
  by_contra hc
  push_neg at hc
  have := YoungDiagram.mem_iff_lt_colLen.mp
    (mem_of_le h (YoungDiagram.mem_iff_lt_colLen.mpr hc : (lam.colLen 0, 0) ∈ mu))
  omega

namespace SkewTab

variable (S : SkewTableau lam mu)

theorem entry_eq_zero_iff {r c : ℕ} (hc : c < lam.rowLen r) :
    S.entry r c = 0 ↔ c < mu.rowLen r := by
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · intro h
    by_contra hm
    have := S.positive (YoungDiagram.mem_iff_lt_rowLen.mpr hc) hm
    omega
  · exact fun h => S.zeros_in h

theorem entry_pos {r c : ℕ} (hc : c < lam.rowLen r) (hm : mu.rowLen r ≤ c) :
    0 < S.entry r c :=
  S.positive (YoungDiagram.mem_iff_lt_rowLen.mpr hc) (by
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega)

theorem entry_mono {r c₁ c₂ : ℕ} (h12 : c₁ ≤ c₂) (h2 : c₂ < lam.rowLen r) :
    S.entry r c₁ ≤ S.entry r c₂ := by
  by_cases hm : (r, c₁) ∈ mu
  · rw [S.zeros_in hm]; exact Nat.zero_le _
  · rcases Nat.eq_or_lt_of_le h12 with rfl | hlt
    · exact le_rfl
    · exact S.row_weak hlt (YoungDiagram.mem_iff_lt_rowLen.mpr h2) hm

/-- `#{c : Ŝ(r, c) = v}`, over row `r` of `λ` (value `0` on `μ`). -/
def rowCount (v r : ℕ) : ℕ := ((range (lam.rowLen r)).filter (fun c => S.entry r c = v)).card

/-- `#{c : Ŝ(r, c) ≤ i}`. -/
def rowLe (i r : ℕ) : ℕ := ((range (lam.rowLen r)).filter (fun c => S.entry r c ≤ i)).card

theorem rowLe_eq_sum (r : ℕ) : ∀ i, rowLe S i r = ∑ v ∈ range (i+1), rowCount S v r
  | 0 => by simp [rowLe, rowCount]
  | i+1 => by
    rw [Finset.sum_range_succ, ← rowLe_eq_sum r i, rowLe, rowLe, rowCount,
      ← card_union_of_disjoint (disjoint_filter.mpr fun c _ h1 h2 => by omega), ← filter_or]
    congr 1
    ext c
    simp only [mem_filter, ← and_or_left, Nat.le_add_one_iff]

theorem entry_le_iff {r c : ℕ} (hc : c < lam.rowLen r) (i : ℕ) :
    S.entry r c ≤ i ↔ c < rowLe S i r :=
  initial_segment _ _ (fun _ _ h12 h2 h => (entry_mono S h12 h2).trans h) hc

theorem rowCount_zero (r : ℕ) : rowCount S 0 r = mu.rowLen r := by
  rw [rowCount]
  conv_rhs => rw [← card_range (mu.rowLen r)]
  congr 1
  ext c
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hc, h⟩; exact (entry_eq_zero_iff S hc).mp h
  · intro h
    have hc := lt_of_lt_of_le h (rowLen_le_of_le S.sub r)
    exact ⟨hc, (entry_eq_zero_iff S hc).mpr h⟩

/-- Cells of the skew row word. -/
noncomputable def wordCells (lam mu : YoungDiagram) : List (ℕ × ℕ) :=
  (rowCells lam).filter (fun p => p ∉ mu.cells)

theorem rowWord_eq : S.rowWord = (wordCells lam mu).map (fun p => S.entry p.1 p.2) := rfl

theorem wordCells_pairwise : (wordCells lam mu).Pairwise RowLE :=
  (rowCells_sorted lam).sublist List.filter_sublist

theorem wordCells_nodup : (wordCells lam mu).Nodup :=
  (rowCells_nodup lam).filter _

theorem mem_wordCells (p : ℕ × ℕ) : p ∈ wordCells lam mu ↔ p ∈ lam.cells ∧ p ∉ mu.cells := by
  simp [wordCells]

/-- `#{p ∈ λ : p is read at or after p₀, Ŝ(p) = b}`. -/
def upperCount (p₀ : ℕ × ℕ) (b : ℕ) : ℕ :=
  (lam.cells.filter (fun p => RowLE p₀ p ∧ S.entry p.1 p.2 = b)).card

theorem RowLE_trans' (a b c : ℕ × ℕ) (h1 : RowLE a b) (h2 : RowLE b c) : RowLE a c := by
  unfold RowLE at *; omega

theorem count_upper (p₀ : ℕ × ℕ) {b : ℕ} (hb : 0 < b) :
    (((wordCells lam mu).filter (fun p => RowLE p₀ p)).map (fun p => S.entry p.1 p.2)).count b =
      upperCount S p₀ b := by
  classical
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((wordCells_nodup).filter _ |>.filter _), upperCount]
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_filter, mem_wordCells, Function.comp, beq_iff_eq,
    decide_eq_true_eq, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, fun hm => ?_⟩, h2⟩, h3⟩
    rw [YoungDiagram.mem_cells] at hm
    rw [S.zeros_in hm] at h3
    omega

theorem upper_isSuffix (p₀ : ℕ × ℕ) :
    ((wordCells lam mu).filter (fun p => RowLE p₀ p)).map (fun p => S.entry p.1 p.2) <:+
      S.rowWord :=
  (filter_isSuffix RowLE _ _ wordCells_pairwise
    (fun _ _ h ha => RowLE_trans' _ _ _ ha h)).map _

/-- Yamanouchi, at an upper set of the reading order. -/
theorem upper_le_of_isLR (hS : IsLR S) (p₀ : ℕ × ℕ) {a : ℕ} (ha : 0 < a) :
    upperCount S p₀ (a+1) ≤ upperCount S p₀ a := by
  rw [← count_upper S p₀ ha, ← count_upper S p₀ (by omega)]
  exact hS _ (upper_isSuffix S p₀) a (a+1) ha (by omega)

theorem isLR_of_upper (h : ∀ p₀ ∈ lam.cells, p₀ ∉ mu.cells → ∀ a, 0 < a →
    upperCount S p₀ (a+1) ≤ upperCount S p₀ a) : IsLR S := by
  intro t ht a b ha hab
  rw [List.suffix_iff_eq_drop] at ht
  rw [ht, rowWord_eq, ← List.map_drop]
  set k := (List.map (fun p => S.entry p.1 p.2) (wordCells lam mu)).length - t.length
  by_cases hk : k < (wordCells lam mu).length
  · rw [drop_eq_filter RowLE (fun _ _ h1 h2 => by unfold RowLE at h1 h2; ext <;> omega)
      (fun a => by unfold RowLE; omega) _ k hk wordCells_pairwise wordCells_nodup,
      count_upper S _ ha, count_upper S _ (by omega)]
    have hmem := (mem_wordCells _).mp (List.get_mem (wordCells lam mu) ⟨k, hk⟩)
    obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - (a+1), by omega⟩
    induction d with
    | zero => exact h _ hmem.1 hmem.2 a ha
    | succ d ih =>
      exact (h _ hmem.1 hmem.2 (a+1+d) (by omega)).trans (ih (by omega))
  · rw [List.drop_eq_nil_of_le (by omega)]
    simp

/-- Row decomposition of `upperCount`. -/
theorem upperCount_eq (r₀ c₀ b : ℕ) :
    upperCount S (r₀, c₀) b = ∑ r ∈ range r₀, rowCount S b r +
      ((range (lam.rowLen r₀)).filter (fun c => c₀ ≤ c ∧ S.entry r₀ c = b)).card := by
  classical
  set N := lam.colLen 0 + r₀ + 1
  rw [upperCount, Finset.card_filter, sum_cells_rows_n lam (n := N) (by omega)]
  have hr : ∀ r ∈ range N, (∑ c ∈ range (lam.rowLen r),
      if RowLE (r₀, c₀) (r, c) ∧ S.entry r c = b then 1 else 0) =
      (if r < r₀ then rowCount S b r else 0) +
        (if r = r₀ then ((range (lam.rowLen r₀)).filter
          (fun c => c₀ ≤ c ∧ S.entry r₀ c = b)).card else 0) := by
    intro r _
    rcases lt_trichotomy r r₀ with h | rfl | h
    · rw [if_pos h, if_neg (by omega), add_zero, rowCount, Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [RowLE, h, true_or, true_and]
    · rw [if_neg (lt_irrefl _), if_pos rfl, zero_add, Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [RowLE, lt_irrefl, true_and, false_or]
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      simp only [RowLE, not_and]
      omega
  rw [Finset.sum_congr rfl hr, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_ite_eq',
    if_pos (by simp; omega)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext r
  simp only [mem_filter, mem_range]
  omega

end SkewTab

end tableau

/-! ## LR tableaux give LR triangles -/

section LR
variable {lam mu : YoungDiagram}
open SkewTab

/-- Column strictness in counts: `#{Ŝ(r+1, ·) ≤ i+1} ≤ #{Ŝ(r, ·) ≤ i}`. -/
theorem rowLe_succ_le (S : SkewTableau lam mu) (i r : ℕ) :
    rowLe S (i+1) (r+1) ≤ rowLe S i r := by
  by_contra h
  push_neg at h
  set Y := rowLe S i r
  have hX : rowLe S (i+1) (r+1) ≤ lam.rowLen (r+1) := by
    rw [rowLe]; exact (card_filter_le _ _).trans (card_range _).le
  have hYr1 : Y < lam.rowLen (r+1) := lt_of_lt_of_le h hX
  have hYr : Y < lam.rowLen r := lt_of_lt_of_le hYr1 (lam.rowLen_anti _ _ (Nat.le_succ r))
  have h1 : S.entry (r+1) Y ≤ i+1 := (entry_le_iff S hYr1 (i+1)).mpr h
  have h2 : ¬ S.entry r Y ≤ i := fun h' => lt_irrefl Y ((entry_le_iff S hYr i).mp h')
  have hm : (r, Y) ∉ mu := fun hm => h2 (by rw [S.zeros_in hm]; exact Nat.zero_le _)
  have h3 := S.col_strict (i₂ := r+1) (Nat.lt_succ_self r)
    (YoungDiagram.mem_iff_lt_rowLen.mpr hYr1) hm
  omega

/-- In an LR tableau the entries of row `r` are at most `r + 1`. -/
theorem entry_le_of_isLR (S : SkewTableau lam mu) (hS : IsLR S) :
    ∀ r c, S.entry r c ≤ r + 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro c
  by_cases hc : c < lam.rowLen r
  swap
  · rw [S.zeros_out (fun h => hc (YoungDiagram.mem_iff_lt_rowLen.mp h))]; exact Nat.zero_le _
  by_contra hb
  push_neg at hb
  obtain ⟨a, ha⟩ : ∃ a, S.entry r c = a + 1 := ⟨S.entry r c - 1, by omega⟩
  have hU : 0 < upperCount S (r, c) (a+1) :=
    card_pos.mpr ⟨(r, c), mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr hc), by unfold RowLE; omega, ha⟩⟩
  have h2 := upper_le_of_isLR S hS (r, c) (a := a) (by omega)
  obtain ⟨p, hp⟩ := card_pos.mp (lt_of_lt_of_le hU h2)
  rw [mem_filter, YoungDiagram.mem_cells] at hp
  obtain ⟨hpl, hrow, hpa⟩ := hp
  unfold RowLE at hrow
  simp only at hrow
  rcases hrow with hlt | ⟨heq, hle⟩
  · have := ih p.1 hlt p.2
    omega
  · have hp2 : p.2 < lam.rowLen r := by
      rw [heq]; exact YoungDiagram.mem_iff_lt_rowLen.mp (by simpa using hpl)
    have := entry_mono S hle hp2
    rw [← heq] at hpa
    omega

theorem rowCount_eq_zero_of_isLR (S : SkewTableau lam mu) (hS : IsLR S) {v r : ℕ}
    (hv : r + 1 < v) : rowCount S v r = 0 := by
  rw [rowCount, card_eq_zero, filter_eq_empty_iff]
  intro c _ h
  have := entry_le_of_isLR S hS r c
  omega

theorem rowLe_eq_rowLen (S : SkewTableau lam mu) (hS : IsLR S) {i r : ℕ} (hi : r + 1 ≤ i) :
    rowLe S i r = lam.rowLen r := by
  rw [rowLe, filter_true_of_mem (fun c _ => (entry_le_of_isLR S hS r c).trans hi), card_range]

/-- `1`-based parts: `part κ j = κ_j`. -/
def part (κ : YoungDiagram) (j : ℕ) : ℤ := κ.rowLen (j - 1)

/-- E (4.11), p. 16: the triangle `A_S`: `a_{0,0} = 0`, `a_{0,j} = μ_j`,
`a_{i,j} = #{entries i in row j of S}` (row `j - 1` of `Ŝ`, zero-based). -/
def AS (n : ℕ) (S : SkewTableau lam mu) : V ℤ n :=
  fun x => if x.j = 0 then 0 else (rowCount S x.i (x.j - 1) : ℤ)

theorem coord_AS (n : ℕ) (S : SkewTableau lam mu) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    coord (AS n S) i j = if j = 0 then 0 else (rowCount S i (j-1) : ℤ) := by
  rw [coord_mk _ hij hj]; rfl

theorem coord_AS_zero (n : ℕ) (S : SkewTableau lam mu) : coord (AS n S) 0 0 = 0 := by
  rw [coord_AS n S le_rfl (Nat.zero_le _), if_pos rfl]

theorem coord_AS_succ (n : ℕ) (S : SkewTableau lam mu) (hS : IsLR S) (i : ℕ) {j : ℕ}
    (hj : j + 1 ≤ n) : coord (AS n S) i (j+1) = rowCount S i j := by
  by_cases hij : i ≤ j + 1
  · rw [coord_AS n S hij hj, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
  · rw [coord_of_lt _ (by omega), rowCount_eq_zero_of_isLR S hS (by omega), Nat.cast_zero]

theorem coord_AS_nonneg (n : ℕ) (S : SkewTableau lam mu) (i j : ℕ) : 0 ≤ coord (AS n S) i j := by
  unfold coord
  split_ifs
  · show 0 ≤ (if _ then _ else _ : ℤ)
    split_ifs <;> simp
  · exact le_rfl

theorem sum_Icc_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a m : ℕ) :
    ∑ q ∈ Icc (a+1) m, f (q-1) = ∑ r ∈ Ico a m, f r := by
  rw [← Nat.Ico_succ_right, ← Finset.sum_Ico_add' (fun q => f (q-1)) a m 1]
  simp

theorem sum_Ico_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a m : ℕ}
    (h : ∀ r < a, f r = 0) : ∑ r ∈ Ico a m, f r = ∑ r ∈ range m, f r := by
  rw [Finset.range_eq_Ico]
  apply Finset.sum_subset
  · intro r hr
    simp only [mem_Ico] at hr ⊢
    omega
  · intro r hr hr'
    simp only [mem_Ico] at hr hr'
    exact h r (by omega)

/-- `content(S)_v = Σ_r #{entries v in row r}`, `v ≥ 1`. -/
theorem content_eq_sum (S : SkewTableau lam mu) {n : ℕ} (hl : lam.colLen 0 ≤ n) {v : ℕ}
    (hv : 0 < v) : S.content v = ∑ r ∈ range n, rowCount S v r := by
  classical
  rw [SkewTableau.content_apply]
  have he : (skewCells lam mu).filter (fun p => S.entry p.1 p.2 = v) =
      lam.cells.filter (fun p => S.entry p.1 p.2 = v) := by
    ext p
    simp only [mem_filter, skewCells, mem_sdiff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun hm => ?_⟩, h2⟩
      rw [YoungDiagram.mem_cells] at hm
      rw [S.zeros_in hm] at h2
      omega
  rw [he, card_filter, sum_cells_rows_n lam hl]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rowCount, card_filter]

variable {nu : YoungDiagram}

/-- E Lemma 4.12, p. 16: `A_S ∈ △_LR(λ, μ, ν)` (corrected Definition 4.11 (3)). -/
theorem AS_mem (n : ℕ) (S : SkewTableau lam mu) (hS : S ∈ lrTableaux lam mu nu)
    (hl : lam.colLen 0 ≤ n) :
    AS n S ∈ triangles n (part lam) (part mu) (part nu) := by
  rw [mem_lrTableaux] at hS
  obtain ⟨hc, hLR⟩ := hS
  refine ⟨⟨coord_AS_zero n S, fun i j _ _ _ => coord_AS_nonneg n S i j, ?_, ?_⟩, ?_⟩
  · -- (2)
    intro i j hi hij hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Finset.sum_congr rfl (fun p _ => coord_AS_succ n S hLR p (j := j+1) hj),
      Finset.sum_congr rfl (fun p _ => coord_AS_succ n S hLR p (j := j) (by omega)),
      ← Nat.cast_sum, ← Nat.cast_sum, ← rowLe_eq_sum, ← rowLe_eq_sum, Nat.cast_le]
    exact rowLe_succ_le S i j
  · -- (3)
    intro i j hi hij hj
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have e1 : ∑ q ∈ Icc (i+1+1) (j+1), coord (AS n S) (i+1+1) q =
        ∑ r ∈ range (j+1), (rowCount S (i+2) r : ℤ) := by
      rw [← sum_Ico_eq_range (fun r => (rowCount S (i+2) r : ℤ)) (a := i+1) (fun r hr => by
          simp only; rw [rowCount_eq_zero_of_isLR S hLR (by omega), Nat.cast_zero]),
        ← sum_Icc_shift (fun r => (rowCount S (i+2) r : ℤ))]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp only [mem_Icc] at hq
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [coord_AS_succ n S hLR _ (by omega), Nat.add_sub_cancel]
    have e2 : ∑ q ∈ Icc (i+1) j, coord (AS n S) (i+1) q = ∑ r ∈ range j, (rowCount S (i+1) r : ℤ) := by
      rw [← sum_Ico_eq_range (fun r => (rowCount S (i+1) r : ℤ)) (a := i) (fun r hr => by
          simp only; rw [rowCount_eq_zero_of_isLR S hLR (by omega), Nat.cast_zero]),
        ← sum_Icc_shift (fun r => (rowCount S (i+1) r : ℤ))]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp only [mem_Icc] at hq
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [coord_AS_succ n S hLR _ (by omega), Nat.add_sub_cancel]
    rw [e1, e2, ← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le]
    have hU := upper_le_of_isLR S hLR (j, rowLe S (i+1) j) (a := i+1) (by omega)
    rw [upperCount_eq, upperCount_eq] at hU
    have hz : ((range (lam.rowLen j)).filter
        (fun c => rowLe S (i+1) j ≤ c ∧ S.entry j c = i+1)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro c hc ⟨h1, h2⟩
      have := (entry_le_iff S (mem_range.mp hc) (i+1)).mp h2.le
      omega
    have ht : ((range (lam.rowLen j)).filter
        (fun c => rowLe S (i+1) j ≤ c ∧ S.entry j c = i+1+1)).card = rowCount S (i+2) j := by
      rw [rowCount]
      congr 1
      ext c
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨h1, ?_, h3⟩
        by_contra h
        push_neg at h
        have := (entry_le_iff S h1 (i+1)).mpr h
        omega
    rw [hz, add_zero, ht, ← Finset.sum_range_succ] at hU
    exact hU
  · intro j h1 hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [lamT, Finset.sum_congr rfl (fun p _ => coord_AS_succ n S hLR p (j := j) hj),
        ← Nat.cast_sum, ← rowLe_eq_sum, rowLe_eq_rowLen S hLR le_rfl, part, Nat.add_sub_cancel]
    · rw [muT, coord_AS_succ n S hLR 0 hj, rowCount_zero, part, Nat.add_sub_cancel]
    · have e : ∑ q ∈ Icc (j+1) n, coord (AS n S) (j+1) q =
          ∑ r ∈ range n, (rowCount S (j+1) r : ℤ) := by
        rw [← sum_Ico_eq_range (fun r => (rowCount S (j+1) r : ℤ)) (a := j) (fun r hr => by
            simp only; rw [rowCount_eq_zero_of_isLR S hLR (by omega), Nat.cast_zero]),
          ← sum_Icc_shift (fun r => (rowCount S (j+1) r : ℤ))]
        refine Finset.sum_congr rfl fun q hq => ?_
        simp only [mem_Icc] at hq
        obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        rw [coord_AS_succ n S hLR _ (by omega), Nat.add_sub_cancel]
      rw [nuT, e, ← Nat.cast_sum, ← content_eq_sum S hl (Nat.succ_pos j), hc, shapeContent_apply,
        part, Nat.add_sub_cancel]

end LR

/-! ## Injectivity -/

section inj
variable {lam mu : YoungDiagram}
open SkewTab

theorem row_lt_of_mem {lam : YoungDiagram} {n r c : ℕ} (hl : lam.colLen 0 ≤ n) (h : (r, c) ∈ lam) :
    r < n := by
  have := YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl (Nat.zero_le c) h)
  omega

/-- E Lemma 4.12, p. 16: `S ↦ A_S` is injective on LR tableaux. -/
theorem AS_injective (n : ℕ) (hl : lam.colLen 0 ≤ n) {S T : SkewTableau lam mu} (hS : IsLR S)
    (hT : IsLR T) (h : AS n S = AS n T) : S = T := by
  apply SkewTableau.ext'
  intro r c
  by_cases hc : c < lam.rowLen r
  swap
  · have hn : (r, c) ∉ lam := fun h => hc (YoungDiagram.mem_iff_lt_rowLen.mp h)
    rw [S.zeros_out hn, T.zeros_out hn]
  have hr : r + 1 ≤ n := row_lt_of_mem hl (YoungDiagram.mem_iff_lt_rowLen.mpr hc)
  have hcnt : ∀ v, rowCount S v r = rowCount T v r := by
    intro v
    have := congrArg (fun A => coord A v (r+1)) h
    simp only at this
    rw [coord_AS_succ n S hS v hr, coord_AS_succ n T hT v hr] at this
    exact_mod_cast this
  have hle : ∀ i, S.entry r c ≤ i ↔ T.entry r c ≤ i := by
    intro i
    rw [entry_le_iff S hc, entry_le_iff T hc, rowLe_eq_sum, rowLe_eq_sum]
    simp only [hcnt]
  exact le_antisymm ((hle _).mpr le_rfl) ((hle _).mp le_rfl)

end inj

/-! ## Surjectivity: the tableau of an integral LR triangle -/

section surj
variable {n : ℕ} {lam mu nu : YoungDiagram}

theorem part_eq_zero {κ : YoungDiagram} (hκ : κ.colLen 0 ≤ n) {r : ℕ} (hr : n ≤ r) :
    κ.rowLen r = 0 := rowLen_eq_zero_of_le (by omega)

theorem diag_nonneg {A : V ℤ n} (hA : A ∈ triangles n (part lam) (part mu) (part nu)) :
    ∀ d p, n = p + d → 1 ≤ p → 0 ≤ coord A p p
  | 0, p, hd, hp => by
    obtain rfl : p = n := by omega
    have := (hA.2 p hp le_rfl).2.2
    rw [nuT, Finset.Icc_self, Finset.sum_singleton, part] at this
    rw [this]; exact Nat.cast_nonneg _
  | d+1, p, hd, hp => by
    have h2 := hA.1.lattice p p hp le_rfl (by omega)
    rw [Finset.Icc_self, Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton] at h2
    exact (diag_nonneg hA d (p+1) (by omega) (by omega)).trans h2

/-- Entries `a_{p,q}`, `p ≥ 1`, of an LR triangle are nonnegative (using `ν_n ≥ 0`). -/
theorem coord_nonneg_of_mem {A : V ℤ n} (hA : A ∈ triangles n (part lam) (part mu) (part nu))
    {p q : ℕ} (hp : 1 ≤ p) : 0 ≤ coord A p q := by
  rcases lt_or_le q p with hqp | hpq
  · rw [coord_of_lt A hqp]
  rcases lt_or_le n q with hnq | hqn
  · rw [coord_of_gt A hnq]
  rcases Nat.lt_or_ge p q with hlt | hge
  · exact hA.1.nonneg p q hp hlt hqn
  obtain rfl : p = q := le_antisymm hpq hge
  exact diag_nonneg hA (n - p) p (by omega) hp

/-- Row prefix sums `C(r, i) = μ_{r+1} + Σ_{p=1}^{i} a_{p,r+1}` of a triangle. -/
def C (A : V ℤ n) (r i : ℕ) : ℤ := ∑ p ∈ range (i+1), coord A p (r+1)

variable {A : V ℤ n} (hA : A ∈ triangles n (part lam) (part mu) (part nu))
  (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
include hA

theorem C_zero (hm : mu.colLen 0 ≤ n) (r : ℕ) : C A r 0 = mu.rowLen r := by
  rw [C, Finset.sum_range_one]
  by_cases hr : r + 1 ≤ n
  · have := (hA.2 (r+1) (Nat.succ_pos r) hr).2.1
    rw [muT, part, Nat.add_sub_cancel] at this
    exact this
  · rw [coord_of_gt A (by omega), part_eq_zero hm (by omega), Nat.cast_zero]

theorem C_mono (r : ℕ) {i i' : ℕ} (h : i ≤ i') : C A r i ≤ C A r i' := by
  unfold C
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp; simp only [mem_range] at hp ⊢; omega
  · intro p hp hp'
    simp only [mem_range, not_lt] at hp hp'
    exact coord_nonneg_of_mem hA (by omega)

theorem C_top (hl : lam.colLen 0 ≤ n) (r : ℕ) {i : ℕ} (hi : r + 1 ≤ i) :
    C A r i = lam.rowLen r := by
  have hsplit : C A r i = C A r (r+1) := by
    unfold C
    symm
    apply Finset.sum_subset
    · intro p hp; simp only [mem_range] at hp ⊢; omega
    · intro p _ hp
      simp only [mem_range, not_lt] at hp
      exact coord_of_lt A (by omega)
  rw [hsplit]
  by_cases hr : r + 1 ≤ n
  · have := (hA.2 (r+1) (Nat.succ_pos r) hr).1
    rw [lamT, part, Nat.add_sub_cancel] at this
    exact this
  · rw [part_eq_zero hl (by omega), Nat.cast_zero, C]
    exact Finset.sum_eq_zero fun p _ => coord_of_gt A (by omega)

theorem C_le (hl : lam.colLen 0 ≤ n) (r i : ℕ) : C A r i ≤ lam.rowLen r := by
  rw [← C_top hA hl r (le_max_right i (r+1))]
  exact C_mono hA r (le_max_left _ _)

theorem mu_le_lam (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) : mu ≤ lam := by
  rw [← YoungDiagram.cells_subset_iff]
  intro p hp
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hp ⊢
  have h1 := C_zero hA hm p.1
  have h2 := C_le hA hl p.1 0
  omega

theorem exists_C (hl : lam.colLen 0 ≤ n) {r c : ℕ} (h : (r, c) ∈ lam) :
    ∃ i, (c : ℤ) < C A r i :=
  ⟨r+1, by rw [C_top hA hl r le_rfl]; exact_mod_cast YoungDiagram.mem_iff_lt_rowLen.mp h⟩

theorem C_nonneg (hm : mu.colLen 0 ≤ n) (r i : ℕ) : 0 ≤ C A r i := by
  have := C_mono hA r (Nat.zero_le i)
  rw [C_zero hA hm] at this
  exact le_trans (Nat.cast_nonneg _) this

open Classical in
/-- The tableau entry of an integral LR triangle: on `λ/μ`, the least `i` with `c < C(r, i)`. -/
noncomputable def tabEntry (hl : lam.colLen 0 ≤ n) (r c : ℕ) : ℕ :=
  if h : (r, c) ∈ lam ∧ (r, c) ∉ mu then Nat.find (exists_C hA hl h.1) else 0

theorem tabEntry_le_iff (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) {r c : ℕ}
    (hc : c < lam.rowLen r) (i : ℕ) : tabEntry hA hl r c ≤ i ↔ (c : ℤ) < C A r i := by
  classical
  have hcl : (r, c) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr hc
  by_cases hcm : (r, c) ∈ mu
  · rw [tabEntry, dif_neg (fun h => h.2 hcm)]
    simp only [Nat.zero_le, true_iff]
    have h1 := C_mono hA r (Nat.zero_le i)
    rw [C_zero hA hm] at h1
    have := YoungDiagram.mem_iff_lt_rowLen.mp hcm
    omega
  · rw [tabEntry, dif_pos ⟨hcl, hcm⟩, Nat.find_le_iff]
    constructor
    · rintro ⟨m, hm', h⟩
      exact lt_of_lt_of_le h (C_mono hA r hm')
    · intro h
      exact ⟨i, le_rfl, h⟩

theorem tabEntry_pos (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) {r c : ℕ}
    (h1 : (r, c) ∈ lam) (h2 : (r, c) ∉ mu) : 0 < tabEntry hA hl r c := by
  have hc := YoungDiagram.mem_iff_lt_rowLen.mp h1
  by_contra h0
  have := (tabEntry_le_iff hA hl hm hc 0).mp (by omega)
  rw [C_zero hA hm] at this
  exact h2 (YoungDiagram.mem_iff_lt_rowLen.mpr (by exact_mod_cast this))

theorem tabEntry_row (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) {r c₁ c₂ : ℕ}
    (h12 : c₁ < c₂) (h2 : (r, c₂) ∈ lam) : tabEntry hA hl r c₁ ≤ tabEntry hA hl r c₂ := by
  have hc2 := YoungDiagram.mem_iff_lt_rowLen.mp h2
  have h := (tabEntry_le_iff hA hl hm hc2 _).mp le_rfl
  exact (tabEntry_le_iff hA hl hm (by omega) _).mpr (lt_trans (by exact_mod_cast h12) h)

theorem tabEntry_col (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) {r c : ℕ}
    (h1 : (r+1, c) ∈ lam) (h0 : (r, c) ∉ mu) :
    tabEntry hA hl r c < tabEntry hA hl (r+1) c := by
  have hc1 := YoungDiagram.mem_iff_lt_rowLen.mp h1
  have hc0 : c < lam.rowLen r := lt_of_lt_of_le hc1 (lam.rowLen_anti _ _ (Nat.le_succ r))
  have hrn : r + 1 < n := row_lt_of_mem hl h1
  have hm1 : (r+1, c) ∉ mu := fun h => h0 (mu.up_left_mem (Nat.le_succ r) le_rfl h)
  set e := tabEntry hA hl (r+1) c with he
  have hepos : 0 < e := tabEntry_pos hA hl hm h1 hm1
  have hce : (c : ℤ) < C A (r+1) e := (tabEntry_le_iff hA hl hm hc1 e).mp le_rfl
  have hC : C A (r+1) e ≤ C A r (e-1) := by
    by_cases hle : e ≤ r + 1
    · have := hA.1.column e (r+1) hepos hle hrn
      unfold C
      rw [show e - 1 + 1 = e by omega]
      exact this
    · calc C A (r+1) e ≤ lam.rowLen (r+1) := C_le hA hl _ _
        _ ≤ lam.rowLen r := by exact_mod_cast lam.rowLen_anti _ _ (Nat.le_succ r)
        _ = C A r (e-1) := (C_top hA hl r (by omega)).symm
  have := (tabEntry_le_iff hA hl hm hc0 (e-1)).mpr (lt_of_lt_of_le hce hC)
  omega

theorem tabEntry_col_strict (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) {i₁ i₂ j : ℕ}
    (h12 : i₁ < i₂) (h2 : (i₂, j) ∈ lam) (h1 : (i₁, j) ∉ mu) :
    tabEntry hA hl i₁ j < tabEntry hA hl i₂ j := by
  obtain ⟨d, rfl⟩ : ∃ d, i₂ = i₁ + d + 1 := ⟨i₂ - i₁ - 1, by omega⟩
  induction d with
  | zero => exact tabEntry_col hA hl hm h2 h1
  | succ d ih =>
    have hmem : (i₁ + d + 1, j) ∈ lam := lam.up_left_mem (by omega) le_rfl h2
    have hnm : (i₁ + d + 1, j) ∉ mu := fun h => h1 (mu.up_left_mem (by omega) le_rfl h)
    exact (ih (by omega) hmem).trans (tabEntry_col hA hl hm (r := i₁ + d + 1) h2 hnm)

open Classical in
/-- The LR tableau of an integral LR triangle (inverse of `S ↦ A_S`). -/
noncomputable def tabOf (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) :
    SkewTableau lam mu where
  entry := tabEntry hA hl
  sub := mu_le_lam hA hl hm
  row_weak := fun h12 h2 _ => tabEntry_row hA hl hm h12 h2
  col_strict := fun h12 h2 h1 => tabEntry_col_strict hA hl hm h12 h2 h1
  zeros_out := fun h => by rw [tabEntry, dif_neg (fun h' => h h'.1)]
  zeros_in := fun h => by rw [tabEntry, dif_neg (fun h' => h'.2 h)]
  positive := fun h1 h2 => tabEntry_pos hA hl hm h1 h2

open SkewTab

theorem rowLe_tabOf (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) (i r : ℕ) :
    (rowLe (tabOf hA hl hm) i r : ℤ) = C A r i := by
  have h0 := C_nonneg hA hm r i
  have h1 := C_le hA hl r i
  have hset : (range (lam.rowLen r)).filter (fun c => (tabOf hA hl hm).entry r c ≤ i) =
      range (C A r i).toNat := by
    ext c
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hc, h⟩
      have := (tabEntry_le_iff hA hl hm hc i).mp h
      omega
    · intro hc
      have hc' : c < lam.rowLen r := by omega
      exact ⟨hc', (tabEntry_le_iff hA hl hm hc' i).mpr (by omega)⟩
  rw [rowLe, hset, card_range]
  omega

theorem rowCount_tabOf (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) (v r : ℕ) :
    (rowCount (tabOf hA hl hm) v r : ℤ) = coord A v (r+1) := by
  rcases v with _ | v
  · have := rowLe_tabOf hA hl hm 0 r
    rw [rowLe_eq_sum, Finset.sum_range_one, C, Finset.sum_range_one] at this
    exact this
  · have h1 := rowLe_tabOf hA hl hm (v+1) r
    have h2 := rowLe_tabOf hA hl hm v r
    have hC : C A r (v+1) = C A r v + coord A (v+1) (r+1) := by
      unfold C; rw [Finset.sum_range_succ]
    rw [rowLe_eq_sum, Finset.sum_range_succ, ← rowLe_eq_sum, Nat.cast_add, h2, hC] at h1
    linarith

omit hA in
theorem sum_coord_row (k m : ℕ) :
    ∑ q ∈ Icc (k+1) m, coord A (k+1) q = ∑ r ∈ range m, coord A (k+1) (r+1) := by
  rw [← sum_Ico_eq_range (fun r => coord A (k+1) (r+1)) (a := k)
      (fun r hr => coord_of_lt A (by omega)),
    ← sum_Icc_shift (fun r => coord A (k+1) (r+1))]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [mem_Icc] at hq
  rw [Nat.sub_add_cancel (by omega)]

theorem tabOf_content (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) (hn : nu.colLen 0 ≤ n) :
    (tabOf hA hl hm).content = TableauDominance.shapeContent nu := by
  ext k
  rcases k with _ | k
  · rw [shapeContent_zero, SkewTableau.content_apply, card_eq_zero, filter_eq_empty_iff]
    rintro ⟨r, c⟩ hp h
    rw [mem_skewCells] at hp
    have := tabEntry_pos hA hl hm hp.1 hp.2
    change tabEntry hA hl r c = 0 at h
    omega
  · rw [content_eq_sum _ hl (Nat.succ_pos k), shapeContent_apply]
    have e : (∑ r ∈ range n, (rowCount (tabOf hA hl hm) (k+1) r : ℤ)) = nu.rowLen k := by
      simp only [rowCount_tabOf]
      by_cases hk : k + 1 ≤ n
      · have := (hA.2 (k+1) (Nat.succ_pos k) hk).2.2
        rw [nuT, sum_coord_row (A := A), part, Nat.add_sub_cancel] at this
        exact this
      · rw [part_eq_zero hn (by omega), Nat.cast_zero]
        exact Finset.sum_eq_zero fun r hr => coord_of_lt A (by simp at hr; omega)
    exact_mod_cast e

theorem tabOf_isLR (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) : IsLR (tabOf hA hl hm) := by
  apply isLR_of_upper
  rintro ⟨r₀, c₀⟩ h0l _ a ha
  have hr₀ : r₀ < n := row_lt_of_mem hl (by simpa using h0l)
  rw [upperCount_eq, upperCount_eq]
  set T := tabOf hA hl hm
  have hX : ((range (lam.rowLen r₀)).filter (fun c => c₀ ≤ c ∧ T.entry r₀ c = a+1)).card ≤
      rowCount T (a+1) r₀ := by
    rw [rowCount]
    exact card_le_card (monotone_filter_right _ fun c h => h.2)
  have key : ∑ r ∈ range (r₀+1), rowCount T (a+1) r ≤ ∑ r ∈ range r₀, rowCount T a r := by
    have hZ : (∑ r ∈ range (r₀+1), (rowCount T (a+1) r : ℤ)) ≤
        ∑ r ∈ range r₀, (rowCount T a r : ℤ) := by
      simp only [T, rowCount_tabOf]
      by_cases har : a ≤ r₀
      · have h3 := hA.1.lattice a r₀ ha har hr₀
        obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        rw [sum_coord_row (A := A), sum_coord_row (A := A)] at h3
        exact h3
      · rw [Finset.sum_eq_zero fun r hr => coord_of_lt A (by simp at hr; omega)]
        exact Finset.sum_nonneg fun r _ => coord_nonneg_of_mem hA ha
    exact_mod_cast hZ
  rw [Finset.sum_range_succ] at key
  omega

theorem AS_tabOf (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) : AS n (tabOf hA hl hm) = A := by
  apply ext_coord
  intro i j hij hj
  rw [coord_AS n _ hij hj]
  split_ifs with h0
  · subst h0
    obtain rfl : i = 0 := by omega
    exact hA.1.zero.symm
  · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, rowCount_tabOf]

end surj

/-- E Lemma 4.12, p. 16, with Definition 4.11 (3) corrected: for `λ, μ, ν` with at most `n`
parts, `S ↦ A_S` is a bijection from the LR tableaux of shape `λ/μ` and content `ν` onto the
integer points of `△_LR(λ, μ, ν)`. -/
theorem lemma_4_12 {lam mu nu : YoungDiagram} (n : ℕ) (hl : lam.colLen 0 ≤ n)
    (hm : mu.colLen 0 ≤ n) (hn : nu.colLen 0 ≤ n) :
    Set.BijOn (AS n) (lrTableaux lam mu nu : Set (SkewTableau lam mu))
      (triangles n (part lam) (part mu) (part nu)) := by
  refine ⟨fun S hS => AS_mem n S hS hl, fun S hS T hT h => ?_, fun A hA => ?_⟩
  · exact AS_injective n hl (mem_lrTableaux.mp hS).2 (mem_lrTableaux.mp hT).2 h
  · refine ⟨tabOf hA hl hm, ?_, AS_tabOf hA hl hm⟩
    exact mem_lrTableaux.mpr ⟨tabOf_content hA hl hm hn, tabOf_isLR hA hl hm⟩

/-! ## `N^<(S) = Q_△(A_S)` -/

section Nlt
variable {lam mu : YoungDiagram}
open SkewTab

/-- `#{c : Ŝ(r, c) < v} = Σ_{u < v} #{c : Ŝ(r, c) = u}`. -/
theorem rowLt_eq_sum (S : SkewTableau lam mu) (r : ℕ) : ∀ v,
    ((range (lam.rowLen r)).filter (fun c => S.entry r c < v)).card =
      ∑ u ∈ range v, rowCount S u r
  | 0 => by simp
  | v+1 => by
    rw [Finset.sum_range_succ, ← rowLt_eq_sum S r v, rowCount,
      ← card_union_of_disjoint (disjoint_filter.mpr fun c _ h1 h2 => by omega), ← filter_or]
    congr 1
    ext c
    simp only [mem_filter, ← and_or_left, Nat.lt_add_one_iff, Nat.le_iff_lt_or_eq]

/-- Grouping a row by values. -/
theorem sum_row_values (S : SkewTableau lam mu) (hS : IsLR S) {n r : ℕ} (hr : r < n)
    (G : ℕ → ℕ) :
    ∑ c ∈ range (lam.rowLen r), G (S.entry r c) =
      ∑ v ∈ range (n+1), rowCount S v r * G v := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := range (n+1)) (g := fun c => S.entry r c)
    (fun c _ => by have := entry_le_of_isLR S hS r c; simp only [mem_range]; omega) G]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_const, smul_eq_mul, rowCount]

/-- `N^<(Ŝ) = Σ_{r} Σ_{v} #{v in row r} · #{entries < v in rows above r}`. -/
theorem Nlt_eq_sum (S : SkewTableau lam mu) (hS : IsLR S) {n : ℕ} (hl : lam.colLen 0 ≤ n) :
    S.Nlt = ∑ r ∈ range n, ∑ v ∈ range (n+1),
      rowCount S v r * ∑ r' ∈ range r, ∑ u ∈ range v, rowCount S u r' := by
  classical
  let lt : ℕ × ℕ → ℕ × ℕ → Prop := fun p q => RowLE p q ∧ p ≠ q
  have hasymm : ∀ a b, lt a b → ¬ lt b a := by
    rintro a b ⟨h1, h2⟩ ⟨h3, -⟩
    apply h2
    unfold RowLE at h1 h3
    ext <;> omega
  have hpw : (rowCells lam).Pairwise lt := (rowCells_sorted lam).and (rowCells_nodup lam)
  have htf : (rowCells lam).toFinset = lam.cells := by
    ext p; simp
  rw [SkewTableau.Nlt, SkewTableau.hatWord,
    inversions_map lt hasymm _ (rowCells lam) hpw (rowCells_nodup lam), htf]
  have hp : ∀ p ∈ lam.cells, (lam.cells.filter (fun q => lt p q ∧
      S.entry q.1 q.2 < S.entry p.1 p.2)).card =
      ∑ r' ∈ range p.1, ∑ u ∈ range (S.entry p.1 p.2), rowCount S u r' := by
    intro p hpc
    rw [YoungDiagram.mem_cells] at hpc
    have hp1 : p.1 < n := row_lt_of_mem hl (show (p.1, p.2) ∈ lam from hpc)
    have hfil : lam.cells.filter (fun q => lt p q ∧ S.entry q.1 q.2 < S.entry p.1 p.2) =
        lam.cells.filter (fun q => q.1 < p.1 ∧ S.entry q.1 q.2 < S.entry p.1 p.2) := by
      apply Finset.filter_congr
      intro q hq
      rw [YoungDiagram.mem_cells] at hq
      simp only [lt, RowLE]
      constructor
      · rintro ⟨⟨h1 | ⟨h1, h2⟩, h3⟩, h4⟩
        · exact ⟨h1, h4⟩
        · exfalso
          have hq2 : q.2 < lam.rowLen p.1 := by
            rw [h1]; exact YoungDiagram.mem_iff_lt_rowLen.mp (show (q.1, q.2) ∈ lam from hq)
          have := entry_mono S h2 hq2
          rw [← h1] at h4
          omega
      · rintro ⟨h1, h4⟩
        exact ⟨⟨Or.inl h1, fun h => by rw [h] at h1; omega⟩, h4⟩
    rw [hfil, card_filter, sum_cells_rows_n lam hl]
    have hr : ∀ r' ∈ range n, (∑ c ∈ range (lam.rowLen r'),
        if r' < p.1 ∧ S.entry r' c < S.entry p.1 p.2 then 1 else 0) =
        if r' < p.1 then ∑ u ∈ range (S.entry p.1 p.2), rowCount S u r' else 0 := by
      intro r' _
      split_ifs with h
      · rw [← rowLt_eq_sum, card_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [h, true_and]
      · exact Finset.sum_eq_zero fun c _ => if_neg (fun h' => h h'.1)
    rw [Finset.sum_congr rfl hr, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext r'
    simp only [mem_filter, mem_range]
    omega
  rw [Finset.sum_congr rfl hp,
    sum_cells_rows_n lam hl (fun p => ∑ r' ∈ range p.1, ∑ u ∈ range (S.entry p.1 p.2),
      rowCount S u r')]
  refine Finset.sum_congr rfl fun r hr => ?_
  exact sum_row_values S hS (mem_range.mp hr)
    (fun v => ∑ r' ∈ range r, ∑ u ∈ range v, rowCount S u r')

theorem Y_AS (n : ℕ) (S : SkewTableau lam mu) (hS : IsLR S) {r : ℕ} (hr : r < n) (v : ℕ) :
    Y (AS n S) v (r+1) = ∑ r' ∈ range r, ∑ u ∈ range v, (rowCount S u r' : ℤ) := by
  have h : ∀ p ∈ range v, ∑ q ∈ Ico p (r+1), coord (AS n S) p q =
      ∑ r' ∈ range r, (rowCount S p r' : ℤ) := by
    intro p _
    rw [sum_Ico_eq_range (fun q => coord (AS n S) p q) (fun q hq => coord_of_lt _ hq),
      Finset.sum_range_succ']
    have h0 : coord (AS n S) p 0 = 0 := by
      rcases p with _ | p
      · exact coord_AS_zero n S
      · exact coord_of_lt _ (Nat.succ_pos p)
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun r' hr' => coord_AS_succ n S hS p (by simp at hr'; omega)
  rw [Y, Finset.sum_congr rfl h, Finset.sum_comm]

/-- E §4.3, p. 17: `N^<(S) = Q_△(A_S)` for an LR tableau `S`. -/
theorem Nlt_eq_Qtri (n : ℕ) (S : SkewTableau lam mu) (hS : IsLR S) (hl : lam.colLen 0 ≤ n) :
    (S.Nlt : ℤ) = Qtri (AS n S) := by
  have hQ : Qtri (AS n S) = ∑ i ∈ range (n+1), ∑ r ∈ range n,
      (rowCount S i r : ℤ) * Y (AS n S) i (r+1) := by
    rw [Qtri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.Ico_succ_right, sum_Ico_eq_range (fun j => coord (AS n S) i j * Y (AS n S) i j)
      (fun j hj => by simp only; rw [coord_of_lt _ hj, zero_mul]), Finset.sum_range_succ']
    have h0 : coord (AS n S) i 0 = 0 := by
      rcases i with _ | i
      · exact coord_AS_zero n S
      · exact coord_of_lt _ (Nat.succ_pos i)
    rw [h0, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun r hr => by
      rw [coord_AS_succ n S hS i (by simp at hr; omega)]
  rw [Nlt_eq_sum S hS hl, hQ]
  conv_rhs => rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun v _ => ?_
  rw [Y_AS n S hS (mem_range.mp hr) v]

/-- E (4.19), p. 19: `N^<(S) = Q_△(A_S) = Q_𝔥(Φ(A_S))`. -/
theorem Nlt_eq_QH (n : ℕ) (S : SkewTableau lam mu) (hS : IsLR S) (hl : lam.colLen 0 ≤ n) :
    (S.Nlt : ℤ) = QH (phi ℤ n (AS n S)) := by
  rw [QH_phi _ (coord_AS_zero n S), Nlt_eq_Qtri n S hS hl]

end Nlt

/-! ## (4.14) and (4.20) -/

section sums
variable {n : ℕ} {lam mu nu : YoungDiagram}

theorem rowLen_le_card (lam : YoungDiagram) (r : ℕ) : lam.rowLen r ≤ lam.card := by
  rw [YoungDiagram.rowLen_eq_card, YoungDiagram.card]
  exact card_le_card (filter_subset _ _)

theorem coord_mem_Icc {A : V ℤ n} (hA : A ∈ triangles n (part lam) (part mu) (part nu))
    (x : Idx n) : A x ∈ Icc (0 : ℤ) lam.card := by
  rw [← coord_idx A x, mem_Icc]
  have hpq := x.i_le_j
  have hq := x.j_le
  have hnn : ∀ p', 0 ≤ coord A p' x.j := by
    intro p'
    rcases Nat.eq_zero_or_pos p' with rfl | hp'
    · rcases Nat.eq_zero_or_pos x.j with h0 | h0
      · rw [h0, hA.1.zero]
      · have := (hA.2 x.j h0 hq).2.1
        rw [muT, part] at this
        rw [this]; exact Nat.cast_nonneg _
    · exact coord_nonneg_of_mem hA hp'
  refine ⟨hnn _, ?_⟩
  rcases Nat.eq_zero_or_pos x.j with h0 | h0
  · have : x.i = 0 := by omega
    rw [this, h0, hA.1.zero]; exact Nat.cast_nonneg _
  · have hlam := (hA.2 x.j h0 hq).1
    rw [lamT, part] at hlam
    calc coord A x.i x.j ≤ ∑ p' ∈ range (x.j+1), coord A p' x.j :=
          Finset.single_le_sum (fun p' _ => hnn p') (mem_range.mpr (by omega))
      _ = _ := hlam
      _ ≤ _ := by exact_mod_cast rowLen_le_card lam _

open Classical in
/-- The integer points `△_LR(λ, μ, ν) ∩ V_ℤ`, as a finite set. -/
noncomputable def trianglePoints (n : ℕ) (lam mu nu : YoungDiagram) : Finset (V ℤ n) :=
  (Fintype.piFinset fun _ => Icc (0 : ℤ) lam.card).filter
    (fun A => A ∈ triangles n (part lam) (part mu) (part nu))

theorem mem_trianglePoints {A : V ℤ n} :
    A ∈ trianglePoints n lam mu nu ↔ A ∈ triangles n (part lam) (part mu) (part nu) := by
  classical
  rw [trianglePoints, mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨coord_mem_Icc h, h⟩⟩

/-- The integer points `𝔥(λ, μ, ν) ∩ V_ℤ`, as a finite set. -/
noncomputable def hivePoints (n : ℕ) (lam mu nu : YoungDiagram) : Finset (V ℤ n) := by
  classical
  exact (trianglePoints n lam mu nu).image (phi ℤ n)

theorem mem_hivePoints {H : V ℤ n} :
    H ∈ hivePoints n lam mu nu ↔ H ∈ hives n (part lam) (part mu) (part nu) := by
  classical
  rw [hivePoints, mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (phi_bijOn _ _ _).mapsTo (mem_trianglePoints.mp hA)
  · intro hH
    obtain ⟨A, hA, rfl⟩ := (phi_bijOn _ _ _).surjOn hH
    exact ⟨A, mem_trianglePoints.mpr hA, rfl⟩

/-- E (4.14), p. 17, right side of Theorem 4.8 as a triangle sum (corrected Definition 4.11 (3)):
`(-1)^{N(μ)+N(λ)} Σ_{S} (-1)^{N^<(S)} = (-1)^{N(μ)+N(λ)} Σ_{A ∈ △_LR(λ,μ,ν) ∩ V_ℤ} (-1)^{Q_△(A)}`,
for `λ, μ, ν` with at most `n` parts. -/
theorem lrSignedCount_eq_triangles (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    (hn : nu.colLen 0 ≤ n) :
    lrSignedCount lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu +
      TableauStripSigns.north lam) *
      ∑ A ∈ trianglePoints n lam mu nu, (-1 : ℤ) ^ (Qtri A).natAbs := by
  rw [lrSignedCount]
  congr 1
  have hb := lemma_4_12 (lam := lam) (mu := mu) (nu := nu) n hl hm hn
  apply Finset.sum_nbij (AS n)
  · intro S hS; exact mem_trianglePoints.mpr (hb.mapsTo hS)
  · exact fun S hS T hT h => hb.injOn hS hT h
  · intro A hA
    obtain ⟨S, hS, rfl⟩ := hb.surjOn (mem_trianglePoints.mp hA)
    exact ⟨S, hS, rfl⟩
  · intro S hS
    rw [SkewTableau.sign, ← Nlt_eq_Qtri n S (mem_lrTableaux.mp hS).2 hl, Int.natAbs_ofNat]

/-- E (4.20), p. 19, right side of Theorem 4.8 as a hive sum (corrected Definition 4.11 (3)):
`(-1)^{N(μ)+N(λ)} Σ_{H ∈ 𝔥(λ,μ,ν) ∩ V_ℤ} (-1)^{Q_𝔥(H)}`. -/
theorem lrSignedCount_eq_hives (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    (hn : nu.colLen 0 ≤ n) :
    lrSignedCount lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu +
      TableauStripSigns.north lam) *
      ∑ H ∈ hivePoints n lam mu nu, (-1 : ℤ) ^ (QH H).natAbs := by
  classical
  rw [lrSignedCount_eq_triangles hl hm hn, hivePoints,
    Finset.sum_image (g := phi ℤ n) (fun A _ B _ h => (phiEquiv ℤ n).injective h)]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [QH_phi A (mem_trianglePoints.mp hA).1.zero]

/-- E (4.14), p. 17, given Theorem 4.8 (4.6). -/
theorem eq_4_14_of_thm_4_8 (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    (hn : nu.colLen 0 ≤ n) (h48 : oddLR lam mu nu = lrSignedCount lam mu nu) :
    oddLR lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
      ∑ A ∈ trianglePoints n lam mu nu, (-1 : ℤ) ^ (Qtri A).natAbs := by
  rw [h48, lrSignedCount_eq_triangles hl hm hn]

/-- E (4.20), p. 19, given Theorem 4.8 (4.6). -/
theorem eq_4_20_of_thm_4_8 (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    (hn : nu.colLen 0 ≤ n) (h48 : oddLR lam mu nu = lrSignedCount lam mu nu) :
    oddLR lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
      ∑ H ∈ hivePoints n lam mu nu, (-1 : ℤ) ^ (QH H).natAbs := by
  rw [h48, lrSignedCount_eq_hives hl hm hn]

/-- (4.14) is equivalent to Theorem 4.8 (4.6). -/
theorem eq_4_14_iff_thm_4_8 (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    (hn : nu.colLen 0 ≤ n) :
    oddLR lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
      ∑ A ∈ trianglePoints n lam mu nu, (-1 : ℤ) ^ (Qtri A).natAbs ↔
    oddLR lam mu nu = lrSignedCount lam mu nu := by
  rw [lrSignedCount_eq_triangles hl hm hn]

end sums

/-! ## The printed Definition 4.11 (3) and (4.14): `λ = (2,2)`, `μ = (2)`, `ν = (1,1)` -/

section printed
set_option synthInstance.maxHeartbeats 200000

/-- The diagram `(2, 2)`. -/
def shape22 : YoungDiagram := YoungDiagram.ofRowLens [2, 2] (by decide)

theorem rowLen_eq {κ : YoungDiagram} {i k : ℕ} (h : ∀ j, (i, j) ∈ κ ↔ j < k) : κ.rowLen i = k := by
  apply le_antisymm
  · by_contra hc
    push_neg at hc
    have := (h k).mp (YoungDiagram.mem_iff_lt_rowLen.mpr hc)
    omega
  · by_contra hc
    push_neg at hc
    have := YoungDiagram.mem_iff_lt_rowLen.mp ((h (κ.rowLen i)).mpr hc)
    omega

theorem mem_shape22 (i j : ℕ) : (i, j) ∈ shape22 ↔ i < 2 ∧ j < 2 := by
  rw [shape22, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [List.length_cons, List.length_nil] at h1
    interval_cases i <;> simp_all
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, ?_⟩
    interval_cases i <;> simpa using h2

theorem parts_22 : part shape22 1 = 2 ∧ part shape22 2 = 2 ∧
    part (TableauExtremal.rowShape 2) 1 = 2 ∧ part (TableauExtremal.rowShape 2) 2 = 0 ∧
    part (OddLRVerticalPieri.column 2) 1 = 1 ∧ part (OddLRVerticalPieri.column 2) 2 = 1 := by
  simp only [part, show (1:ℕ) - 1 = 0 from rfl, show (2:ℕ) - 1 = 1 from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_cast
  · exact rowLen_eq fun j => by rw [mem_shape22]; omega
  · exact rowLen_eq fun j => by rw [mem_shape22]; omega
  · exact rowLen_eq fun j => by rw [TableauExtremal.mem_rowShape]; omega
  · exact rowLen_eq fun j => by rw [TableauExtremal.mem_rowShape]; omega
  · exact rowLen_eq fun j => by rw [OddLRVerticalPieri.mem_column]; omega
  · exact rowLen_eq fun j => by rw [OddLRVerticalPieri.mem_column]; omega

theorem colLen_le {κ : YoungDiagram} {k : ℕ} (h : ∀ j, (k, j) ∉ κ) : κ.colLen 0 ≤ k := by
  by_contra hc
  exact h 0 (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))

theorem colLen_shape22 : shape22.colLen 0 ≤ 2 :=
  colLen_le fun j => by rw [mem_shape22]; omega
theorem colLen_row2 : (TableauExtremal.rowShape 2).colLen 0 ≤ 2 :=
  colLen_le fun j => by rw [TableauExtremal.mem_rowShape]; omega
theorem colLen_col2 : (OddLRVerticalPieri.column 2).colLen 0 ≤ 2 :=
  colLen_le fun j => by rw [OddLRVerticalPieri.mem_column]; omega

theorem triangles_22 : triangles 2 (part shape22) (part (TableauExtremal.rowShape 2))
    (part (OddLRVerticalPieri.column 2)) = triangles 2 lam22 mu2 nu11 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := parts_22
  ext A
  simp only [triangles, Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj1 =>
    imp_congr_right fun hj2 => ?_
  interval_cases j <;> simp [h1, h2, h3, h4, h5, h6, lam22, mu2, nu11]

theorem trianglesPrinted_22 : trianglesPrinted 2 (part shape22)
    (part (TableauExtremal.rowShape 2)) (part (OddLRVerticalPieri.column 2)) =
    trianglesPrinted 2 lam22 mu2 nu11 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := parts_22
  ext A
  simp only [trianglesPrinted, Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj1 =>
    imp_congr_right fun hj2 => ?_
  interval_cases j <;> simp [h1, h2, h3, h4, h5, h6, lam22, mu2, nu11]

/-- There is no LR tableau of shape `(2,2)/(2)` and content `(1,1)`. -/
theorem lrTableaux_22 :
    lrTableaux shape22 (TableauExtremal.rowShape 2) (OddLRVerticalPieri.column 2) = ∅ := by
  apply Finset.eq_empty_of_forall_not_mem
  intro S hS
  have := AS_mem 2 S hS colLen_shape22
  rw [triangles_22, corrected_empty] at this
  exact this

theorem not_vertical_22 : ¬ OddLRVerticalPieri.Vertical (TableauExtremal.rowShape 2) shape22 := by
  rintro ⟨-, h⟩
  have := h (1, 0) (by
      rw [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_shape22,
        TableauExtremal.mem_rowShape]; omega)
    (1, 1) (by
      rw [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_shape22,
        TableauExtremal.mem_rowShape]; omega) rfl
  simp at this

/-- `c^{(2,2)}_{(2),(1,1)} = 0` (E Remark before Lemma 4.7: the Pieri rule). -/
theorem oddLR_22 : oddLR shape22 (TableauExtremal.rowShape 2) (OddLRVerticalPieri.column 2) = 0 := by
  classical
  letI := DegreeShapes.degreeFintype ((TableauExtremal.rowShape 2).card + 2)
  unfold oddLR
  rw [EKLSectionTwo.vertical_pieri_Q, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun κ _ => ?_
  split_ifs with hv
  · rw [map_zsmul, Finsupp.smul_apply, ← OddGrassmannSchur.sBasis_apply, Basis.repr_self,
      Finsupp.single_apply, if_neg, smul_zero]
    intro he
    rw [he] at hv
    exact not_vertical_22 hv
  · rw [map_zero, Finsupp.zero_apply]

theorem Qtri_cex : Qtri cex = 4 := by decide

/-- E Lemma 4.12 fails for the printed Definition 4.11 (3) (even with `a_{0,0} = 0` imposed):
`cex` is an integer point of the printed `△_LR((2,2),(2),(1,1))` but there is no LR tableau of
shape `(2,2)/(2)` and content `(1,1)`. -/
theorem printed_lemma_4_12_fails :
    ¬ Set.SurjOn (AS 2)
      (lrTableaux shape22 (TableauExtremal.rowShape 2) (OddLRVerticalPieri.column 2) :
        Set (SkewTableau shape22 (TableauExtremal.rowShape 2)))
      (trianglesPrinted 2 (part shape22) (part (TableauExtremal.rowShape 2))
        (part (OddLRVerticalPieri.column 2)) ∩ {A | coord A 0 0 = 0}) := by
  intro h
  have hc : cex ∈ trianglesPrinted 2 (part shape22) (part (TableauExtremal.rowShape 2))
      (part (OddLRVerticalPieri.column 2)) ∩ {A | coord A 0 0 = 0} :=
    ⟨trianglesPrinted_22 ▸ cex_mem_printed, by rw [Set.mem_setOf_eq, coord_cex]; rfl⟩
  obtain ⟨S, hS, -⟩ := h hc
  rw [Finset.mem_coe, lrTableaux_22] at hS
  exact Finset.not_mem_empty S hS

/-- E (4.14) fails for the printed Definition 4.11 (3): for `n = 2`, `λ = (2,2)`, `μ = (2)`,
`ν = (1,1)`, the printed `△_LR(λ, μ, ν) ∩ V_ℤ ∩ {a_{0,0} = 0}` is `{cex}` and the printed
right side `(-1)^{N(μ)+N(λ)} Σ_A (-1)^{Q_△(A)}` equals `1`, while `c^λ_{μν} = 0` and the
corrected right side (4.6) is `0`. -/
theorem printed_4_14_fails :
    trianglesPrinted 2 lam22 mu2 nu11 ∩ {A | coord A 0 0 = 0} = {cex} ∧
      (-1 : ℤ) ^ (TableauStripSigns.north (TableauExtremal.rowShape 2) +
        TableauStripSigns.north shape22) * (-1) ^ (Qtri cex).natAbs = 1 ∧
      oddLR shape22 (TableauExtremal.rowShape 2) (OddLRVerticalPieri.column 2) = 0 ∧
      lrSignedCount shape22 (TableauExtremal.rowShape 2) (OddLRVerticalPieri.column 2) = 0 := by
  refine ⟨?_, ?_, oddLR_22, ?_⟩
  · ext A
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact printed_points A h1 h2
    · rintro rfl
      exact ⟨cex_mem_printed, by rw [coord_cex]; rfl⟩
  · rw [OddLRMisc.north_rowShape, Qtri_cex]
    have : TableauStripSigns.north shape22 = 4 := by decide
    rw [this]; norm_num
  · rw [lrSignedCount, lrTableaux_22, Finset.sum_empty, mul_zero]

end printed

end OddMath.Frontier.OddLRHive

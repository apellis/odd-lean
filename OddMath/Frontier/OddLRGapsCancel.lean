import OddMath.Frontier.OddLRExamplesTools
import OddMath.Frontier.OddLRRuleExample
import OddMath.Frontier.OddLREvenExample

/-!
# `c^{321}_{21,21}` is the first cancellation

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), Example 4.9, p. 15:
"The first interesting cancellation is `c^{(3,2,1)}_{(2,1)(2,1)} = 0` (in the even case, it
equals `2`)."

By Theorem 4.8 (`OddLRRule.thm_4_8`), `c^λ_{μν} = ±Σ_S (-1)^{N^<(S)}` over the Littlewood–Richardson
tableaux `S` of shape `λ/μ` and content `ν`, and by Theorem 4.1 (`OddLREven.thm_4_1`) the even
coefficient is their number; so always `|c^λ_{μν}| ≤ c^λ_{μν}(even)`, with equality iff the signs
do not cancel. `first_cancellation`: for all partitions `λ, μ, ν` with `|λ| ≤ 6`,
`|c^λ_{μν}| = c^λ_{μν}(even)` unless `(λ, μ, ν) = ((3,2,1), (2,1), (2,1))`, where
`c = 0 ≠ 2` (`OddLRRule.example_4_9`).

The proof enumerates the Littlewood–Richardson tableaux as their row words: Yamanouchi words
are generated suffix by suffix (`wordsY`, `mem_wordsY`), a word is the row word of a skew
tableau iff it satisfies `OddLRExamples.ValidW` (`sum_lrTableaux_eq`), and `N^<(S)` is read from
the row word (`hatWord_eq`). The resulting finite check over all `|λ| ≤ 6` is decided by the
kernel (`checkN_eq_true`).
-/

namespace OddMath.Frontier.OddLRGaps

open scoped BigOperators
open TableauSign TableauContent TableauRowWord OddLRTableau OddLRRule OddLREven OddLRExamples

/-! ## Yamanouchi words, suffix by suffix -/

/-- The lattice condition at the head of a word, as in `OddLRExamples.yamB`. -/
def goodB (B : ℕ) (w : List ℕ) : Bool := decide (∀ c < B, 0 < c → w.count (c + 1) ≤ w.count c)

theorem yamB_cons (B a : ℕ) (w : List ℕ) : yamB B (a :: w) = (goodB B (a :: w) && yamB B w) := rfl

/-- The Yamanouchi words of length `n` in the letters `1, …, B`. -/
def wordsY (B : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range B).flatMap (fun a => ((wordsY B n).map ((a + 1) :: ·)).filter (goodB B))

theorem mem_wordsY {B : ℕ} : ∀ {n : ℕ} {v : List ℕ},
    v ∈ wordsY B n ↔ v.length = n ∧ (∀ x ∈ v, 0 < x ∧ x ≤ B) ∧ yamB B v = true
  | 0, v => by
    simp only [wordsY, List.mem_singleton]
    constructor
    · rintro rfl; simp [yamB]
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | n + 1, v => by
    simp only [wordsY, List.mem_flatMap, List.mem_range, List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨a, ha, ⟨u, hu, rfl⟩, hg⟩
      rw [mem_wordsY] at hu
      refine ⟨by simp [hu.1], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hu.2.1 x hx
      · rw [yamB_cons, hg, hu.2.2]; rfl
    · rintro ⟨hl, hv, hy⟩
      rcases v with _ | ⟨a, u⟩
      · simp at hl
      · have ha := hv a List.mem_cons_self
        rw [yamB_cons, Bool.and_eq_true] at hy
        refine ⟨a - 1, by omega, ⟨u, ?_, by rw [show a - 1 + 1 = a by omega]⟩, ?_⟩
        · rw [mem_wordsY]
          exact ⟨by simpa using hl, fun x hx => hv x (List.mem_cons_of_mem _ hx), hy.2⟩
        · simpa [show a - 1 + 1 = a by omega] using hy.1

theorem wordsY_nodup (B : ℕ) : ∀ n, (wordsY B n).Nodup
  | 0 => List.nodup_singleton _
  | n + 1 => by
    unfold wordsY
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => ((wordsY_nodup B n).map (fun u u' h => by simpa using h)).filter _, ?_⟩
    refine List.pairwise_lt_range.imp (fun {a b} h => ?_)
    intro x hx hy
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hx).1
    obtain ⟨u', -, h'⟩ := List.mem_map.mp (List.mem_filter.mp hy).1
    simp only [List.cons.injEq] at h'
    omega

/-! ## Sums over Littlewood–Richardson tableaux as sums over words -/

/-- The row words of the Littlewood–Richardson tableaux on the cells `L` (in reading order) with
content `nw`. -/
def lrWords (L : List (ℕ × ℕ)) (nw : List ℕ) : List (List ℕ) :=
  (wordsY nw.length L.length).filter (fun v =>
    decide (∀ c < nw.length, v.count (c + 1) = nw.getD c 0) && decide (ValidW L v))

theorem sum_lrTableaux_eq {lam mu : YoungDiagram} {L : List (ℕ × ℕ)} (hL : cellsL lam mu = L)
    (hsub : mu.cells ⊆ lam.cells) (nw : List ℕ) (hnw : nw.Sorted (· ≥ ·)) (G : List ℕ → ℤ) :
    ∑ S ∈ lrTableaux lam mu (YoungDiagram.ofRowLens nw hnw), G S.rowWord =
      ((lrWords L nw).map G).sum := by
  classical
  set B := nw.length
  set nu := YoungDiagram.ofRowLens nw hnw
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
  rw [lrWords, ← List.sum_toFinset _ ((wordsY_nodup B _).filter _)]
  apply Finset.sum_bij (fun S _ => S.rowWord)
  · intro S hS
    obtain ⟨hc, hy⟩ := mem_lrTableaux.mp hS
    obtain ⟨hb, hcount⟩ := (hcont S).mp hc
    have hv := validW_rowWord hL S
    rw [List.mem_toFinset, List.mem_filter, mem_wordsY]
    refine ⟨⟨hv.1, hb, (yamB_iff B _ (fun x hx => (hb x hx).2)).mpr hy⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hcount, hv⟩
  · intro S _ S' _ h
    exact ext_of_rowWord h
  · intro v hv
    rw [List.mem_toFinset, List.mem_filter, mem_wordsY] at hv
    obtain ⟨⟨hl, hb, hy⟩, hv⟩ := hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hcount, hvalid⟩ := hv
    refine ⟨ofWord lam mu L hL hsub v hvalid, ?_, rowWord_ofWord hL hsub v hvalid⟩
    rw [mem_lrTableaux, hcont]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [rowWord_ofWord]; exact hb
    · rw [rowWord_ofWord]; exact hcount
    · unfold IsLR
      rw [rowWord_ofWord]
      exact (yamB_iff B v (fun x hx => (hb x hx).2)).mp hy
  · intro S _
    rfl

/-! ## Explicit shapes -/

/-- Membership in the diagram with row lengths `mw`, as a Boolean. -/
def inMu (mw : List ℕ) (p : ℕ × ℕ) : Bool := decide (p.1 < mw.length ∧ p.2 < mw.getD p.1 0)

/-- The cells of `λ/μ` in reading order, for explicit row lengths. -/
def cellsOf (lw mw : List ℕ) : List (ℕ × ℕ) := (rowCellsOf lw).filter (fun p => !inMu mw p)

/-- The row word of `Ŝ` (E §4.2, `j = 0`) in terms of the row word `v` of `S`. -/
def hatOf (lw mw : List ℕ) (v : List ℕ) : List ℕ :=
  (rowCellsOf lw).map (fun p => if inMu mw p then 0 else v.getD (idx (cellsOf lw mw) p) 0)

theorem inMu_iff {mw : List ℕ} (hmw : mw.Sorted (· ≥ ·)) (p : ℕ × ℕ) :
    inMu mw p = true ↔ p ∈ YoungDiagram.ofRowLens mw hmw := by
  rw [mem_ofRowLens_iff, inMu, decide_eq_true_iff]

theorem cellsL_eq_cellsOf {lw mw : List ℕ} (hlw : lw.Sorted (· ≥ ·)) (hmw : mw.Sorted (· ≥ ·)) :
    cellsL (YoungDiagram.ofRowLens lw hlw) (YoungDiagram.ofRowLens mw hmw) = cellsOf lw mw := by
  rw [cellsL_ofRowLens, cellsOf]
  apply List.filter_congr
  intro p _
  have hi := inMu_iff hmw p
  by_cases h : inMu mw p = true
  · have hp : p ∈ (YoungDiagram.ofRowLens mw hmw).cells := (YoungDiagram.mem_cells _).mpr (hi.mp h)
    simp [h, hp]
  · have hp : p ∉ (YoungDiagram.ofRowLens mw hmw).cells :=
      fun hp => h (hi.mpr ((YoungDiagram.mem_cells _).mp hp))
    simp [h, hp]

theorem hatWord_eq {lw mw : List ℕ} (hlw : lw.Sorted (· ≥ ·)) (hmw : mw.Sorted (· ≥ ·))
    (S : SkewTableau (YoungDiagram.ofRowLens lw hlw) (YoungDiagram.ofRowLens mw hmw)) :
    S.hatWord = hatOf lw mw S.rowWord := by
  unfold SkewTableau.hatWord hatOf
  rw [rowCells_ofRowLens]
  apply List.map_congr_left
  intro p hp
  have hpl : p ∈ YoungDiagram.ofRowLens lw hlw := mem_ofRowLens_iff.mpr (mem_rowCellsOf.mp hp)
  by_cases hm : inMu mw p = true
  · rw [if_pos hm]
    exact S.zeros_in ((inMu_iff hmw p).mp hm)
  · rw [if_neg hm]
    have hpm : p ∉ YoungDiagram.ofRowLens mw hmw := fun h => hm ((inMu_iff hmw p).mpr h)
    have hL := cellsL_eq_cellsOf hlw hmw
    have hpL : p ∈ cellsOf lw mw := hL ▸ mem_cellsL.mpr ⟨hpl, hpm⟩
    have hi := idx_lt hpL
    rw [rowWord_eq_map, hL, getD_eq _ _ _ (by simpa using hi), List.getElem_map, getElem_idx hi]

/-- The signed count `Σ_S (-1)^{N^<(S)}`, by computation. -/
def signedL (lw mw nw : List ℕ) : ℤ :=
  ((lrWords (cellsOf lw mw) nw).map (fun v => (-1 : ℤ) ^ inversions (hatOf lw mw v))).sum

/-- The number of Littlewood–Richardson tableaux, by computation. -/
def countL (lw mw nw : List ℕ) : ℤ :=
  ((lrWords (cellsOf lw mw) nw).map (fun _ => (1 : ℤ))).sum

theorem sum_sign_eq {lw mw nw : List ℕ} (hlw : lw.Sorted (· ≥ ·)) (hmw : mw.Sorted (· ≥ ·))
    (hnw : nw.Sorted (· ≥ ·))
    (hsub : (YoungDiagram.ofRowLens mw hmw).cells ⊆ (YoungDiagram.ofRowLens lw hlw).cells) :
    ∑ S ∈ lrTableaux (YoungDiagram.ofRowLens lw hlw) (YoungDiagram.ofRowLens mw hmw)
      (YoungDiagram.ofRowLens nw hnw), S.sign = signedL lw mw nw := by
  rw [signedL, ← sum_lrTableaux_eq (cellsL_eq_cellsOf hlw hmw) hsub nw hnw]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [SkewTableau.sign, SkewTableau.Nlt, hatWord_eq]

theorem card_eq_countL {lw mw nw : List ℕ} (hlw : lw.Sorted (· ≥ ·)) (hmw : mw.Sorted (· ≥ ·))
    (hnw : nw.Sorted (· ≥ ·))
    (hsub : (YoungDiagram.ofRowLens mw hmw).cells ⊆ (YoungDiagram.ofRowLens lw hlw).cells) :
    ((lrTableaux (YoungDiagram.ofRowLens lw hlw) (YoungDiagram.ofRowLens mw hmw)
      (YoungDiagram.ofRowLens nw hnw)).card : ℤ) = countL lw mw nw := by
  rw [countL, ← sum_lrTableaux_eq (cellsL_eq_cellsOf hlw hmw) hsub nw hnw, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one]

/-! ## The finite check -/

/-- For all `λ ⊢ n`, `μ ⊢ k ≤ n`, `ν ⊢ n - k`: no cancellation except at `((3,2,1),(2,1),(2,1))`. -/
def checkN (n : ℕ) : Bool := (partsF n n n).all fun lw => (List.range (n + 1)).all fun k =>
  (partsF k k k).all fun mw => (partsF (n - k) (n - k) (n - k)).all fun nw =>
    decide (|signedL lw mw nw| = countL lw mw nw ↔ ¬(lw = [3, 2, 1] ∧ mw = [2, 1] ∧ nw = [2, 1]))

set_option maxRecDepth 100000 in
theorem checkN_eq_true : ∀ n ≤ 6, checkN n = true := by
  intro n hn
  interval_cases n
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem key {lam mu nu : YoungDiagram} {n k : ℕ} {lw mw nw : List ℕ} (hlw : lw.Sorted (· ≥ ·))
    (hmw : mw.Sorted (· ≥ ·)) (hnw : nw.Sorted (· ≥ ·)) (hlam : lam = YoungDiagram.ofRowLens lw hlw)
    (hmu : mu = YoungDiagram.ofRowLens mw hmw) (hnu : nu = YoungDiagram.ofRowLens nw hnw)
    (hn6 : n ≤ 6) (hk : k ≤ n) (hl : lw ∈ partsF n n n) (hm : mw ∈ partsF k k k)
    (hn : nw ∈ partsF (n - k) (n - k) (n - k)) (hsub : mu.cells ⊆ lam.cells) :
    |∑ S ∈ lrTableaux lam mu nu, S.sign| = ((lrTableaux lam mu nu).card : ℤ) ↔
      ¬(lw = [3, 2, 1] ∧ mw = [2, 1] ∧ nw = [2, 1]) := by
  subst hlam hmu hnu
  rw [sum_sign_eq hlw hmw hnw hsub, card_eq_countL hlw hmw hnw hsub]
  have h := checkN_eq_true n hn6
  simp only [checkN, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact h lw hl k (by omega) mw hm nw hn

/-! ## Example 4.9 -/

theorem rowLens_shape321 : OddLRRule.shape321.rowLens = [3, 2, 1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (by decide)

theorem rowLens_shape21 : OddLRRule.shape21.rowLens = [2, 1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (by decide)

theorem eq_shape_iff (lam κ : YoungDiagram) : lam = κ ↔ lam.rowLens = κ.rowLens :=
  eq_iff_rowLens lam κ

/-- **E Example 4.9**: `c^{(3,2,1)}_{(2,1)(2,1)}` is the first cancellation. For all partitions
`λ, μ, ν` with `|λ| ≤ 6`, the odd Littlewood–Richardson coefficient has the absolute value of the
even one, `|c^λ_{μν}| = c^λ_{μν}(even)`, except for `(λ, μ, ν) = ((3,2,1), (2,1), (2,1))`. -/
theorem first_cancellation (lam mu nu : YoungDiagram) (h6 : lam.card ≤ 6) :
    |oddLR lam mu nu| = OddLREven.evenLR lam mu nu ↔
      ¬(lam = OddLRRule.shape321 ∧ mu = OddLRRule.shape21 ∧ nu = OddLRRule.shape21) := by
  rw [thm_4_8, OddLREven.thm_4_1, lrSignedCount, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]
  have hc321 : OddLRRule.shape321.card = 6 := by
    rw [OddLRRule.shape321, EKPartitionSpanning.card_ofRowLens]; rfl
  have hc21 : OddLRRule.shape21.card = 3 := by
    rw [OddLRRule.shape21, EKPartitionSpanning.card_ofRowLens]; rfl
  have hsub21 : OddLRRule.shape21.cells ⊆ OddLRRule.shape321.cells := by decide
  by_cases hsub : mu.cells ⊆ lam.cells
  swap
  · have he := Finset.card_eq_zero.mp (card_lrTableaux_of_not_sub (nu := nu) hsub)
    rw [he, Finset.sum_empty, Finset.card_empty]
    simp only [abs_zero, Nat.cast_zero, true_iff]
    rintro ⟨rfl, rfl, rfl⟩
    exact hsub hsub21
  by_cases hc : lam.card = mu.card + nu.card
  swap
  · rw [lrTableaux_eq_empty hc, Finset.sum_empty, Finset.card_empty]
    simp only [abs_zero, Nat.cast_zero, true_iff]
    rintro ⟨rfl, rfl, rfl⟩
    exact hc (by rw [hc321, hc21])
  have hmu : mu.card ≤ lam.card := Finset.card_le_card hsub
  have hnu : nu.rowLens ∈ partsF (lam.card - mu.card) (lam.card - mu.card) (lam.card - mu.card) := by
    rw [show lam.card - mu.card = nu.card by omega]
    exact rowLens_mem_partsF nu
  rw [key (n := lam.card) (k := mu.card) lam.rowLens_sorted mu.rowLens_sorted nu.rowLens_sorted
      YoungDiagram.ofRowLens_to_rowLens_eq_self.symm YoungDiagram.ofRowLens_to_rowLens_eq_self.symm
      YoungDiagram.ofRowLens_to_rowLens_eq_self.symm h6 hmu (rowLens_mem_partsF lam)
      (rowLens_mem_partsF mu) hnu hsub,
    eq_shape_iff lam, eq_shape_iff mu, eq_shape_iff nu, rowLens_shape321, rowLens_shape21]

end OddMath.Frontier.OddLRGaps

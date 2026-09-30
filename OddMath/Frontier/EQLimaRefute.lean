import OddMath.Frontier.EQLimaPolyAlg
import OddMath.Frontier.OddLREvenRule

/-!
# Ellis–Qi, proof of Proposition A.3: two printed claims that fail

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2, proof of
Proposition A.3:

  "For Lima partitions, the odd Littlewood–Richardson coefficients of [Ell13, Theorem 4.8] are
  equal to the usual (even) Littlewood–Richardson coefficients. In particular, Lima Schur
  functions pairwise commute."

and (A.1), whose non-leading coefficients `a_μ` are asserted to be non-negative integers.

* `oddLR_431_22_22`: `c^{(4,3,1)}_{(2,2),(2,2)} = -1` while the even coefficient is `1`
  (`evenLR_431_22_22`): for Lima `μ = ν = (2,2)` the odd and even coefficients differ; and
  `s_{(2,2)} s_{(2,2)}` has the coefficient `-1 < 0` at `s_{(4,3,1)}`, with `(4,3,1)` strictly
  dominating `(2,2,2,2)`, contradicting the non-negativity in (A.1).
* `lima_schur_not_comm`: `s_{(4,4,2,2)} s_{(2,2)} ≠ s_{(2,2)} s_{(4,4,2,2)}` in `OΛ`: Lima Schur
  functions do not pairwise commute. (Their coefficients differ at `λ = (6,4,3,2,1)`, which is
  not a Lima partition.)

What is true, and is what the proof of Proposition A.3 needs, is proved elsewhere:
`oddLR_comm_of_lima` (symmetry for Lima `λ, μ, ν`), whence `H(OΛ)` is commutative, and the
dominance bounds of `EQLimaLR`. (Numerically, the odd and even coefficients also differ for some
triples of Lima partitions, e.g. `c^{(6,6,4,4,2,2)}_{(4,4,2,2),(4,4,2,2)} = 2` against `6`; this
is not formalized here.)
-/

namespace OddMath.Frontier.EQLima

open OddLRTableau (SkewTableau lrTableaux mem_lrTableaux IsLR oddLR lrSignedCount)
open OddLREKIdentification (sK)
open OddGrassmannSchur (sBasis)

/-- `(4,3,1)`. -/
def yd431 : YoungDiagram := YoungDiagram.ofRowLens [4, 3, 1] (by decide)

/-- `(2,2)`. -/
def yd22 : YoungDiagram := YoungDiagram.ofRowLens [2, 2] (by decide)

/-- `(4,4,2,2)`. -/
def yd4422 : YoungDiagram := YoungDiagram.ofRowLens [4, 4, 2, 2] (by decide)

/-- `(6,4,3,2,1)`. -/
def yd64321 : YoungDiagram := YoungDiagram.ofRowLens [6, 4, 3, 2, 1] (by decide)

theorem rowLen_ofRowLens' (w : List ℕ) (hw : w.Pairwise (· ≥ ·)) (i : ℕ) :
    (YoungDiagram.ofRowLens w hw.sortedGE).rowLen i = w.getD i 0 := by
  apply rowLen_eq_of
  intro j
  rw [OddLRExamples.mem_ofRowLens_iff (hw := hw)]
  simp only
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h
    omega

theorem isLima_yd22 : IsLima yd22 := by
  intro k
  rw [yd22, rowLen_ofRowLens' [2, 2] (by decide), rowLen_ofRowLens' [2, 2] (by decide)]
  rcases k with _ | k
  · exact ⟨⟨1, rfl⟩, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega), List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
    exact ⟨⟨0, rfl⟩, rfl⟩

theorem isLima_yd4422 : IsLima yd4422 := by
  intro k
  rw [yd4422, rowLen_ofRowLens' [4, 4, 2, 2] (by decide),
    rowLen_ofRowLens' [4, 4, 2, 2] (by decide)]
  rcases k with _ | _ | k
  · exact ⟨⟨2, rfl⟩, rfl⟩
  · exact ⟨⟨1, rfl⟩, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega), List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
    exact ⟨⟨0, rfl⟩, rfl⟩

/-! ### `c^{(4,3,1)}_{(2,2),(2,2)} = -1` -/

theorem cellsL_431 : OddLREven.cellsL yd431 yd22 = [(2, 0), (1, 2), (0, 2), (0, 3)] := by
  rw [yd431, OddLRExamples.cellsL_ofRowLens [4, 3, 1] (by decide)]
  decide

theorem sub_431 : yd22.cells ⊆ yd431.cells := by decide

/-- The unique LR tableau of shape `(4,3,1)/(2,2)` and content `(2,2)`. -/
def tab431 : SkewTableau yd431 yd22 :=
  OddLRExamples.ofWord yd431 yd22 _ cellsL_431 sub_431 [2, 2, 1, 1] (by decide)

theorem shapeContent_22 (k : ℕ) :
    TableauDominance.shapeContent yd22 k = [2, 2, 1, 1].count k := by
  rcases k with _ | k
  · rw [OddLRExamples.shapeContent_zero']; decide
  · rw [yd22, OddLRExamples.shapeContent_ofRowLens [2, 2] (by decide)]
    rcases k with _ | _ | k
    · decide
    · decide
    · rw [List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega), eq_comm]
      exact List.count_eq_zero_of_not_mem (by simp)

theorem tab431_mem : tab431 ∈ lrTableaux yd431 yd22 yd22 := by
  rw [mem_lrTableaux]
  constructor
  · ext k
    rw [OddLRRule.skew_content_eq_count, tab431, OddLRExamples.rowWord_ofWord, shapeContent_22]
  · unfold IsLR
    rw [tab431, OddLRExamples.rowWord_ofWord]
    exact (OddLRExamples.yamB_iff 2 _ (by decide)).mp (by decide)

theorem lrTableaux_431 : lrTableaux yd431 yd22 yd22 = {tab431} := by
  have hcard : (lrTableaux yd431 yd22 yd22).card = 1 := by
    have := OddLRExamples.card_lrTableaux_eq cellsL_431 sub_431 [2, 2] (by decide)
    exact this.trans (by decide)
  obtain ⟨T, hT⟩ := Finset.card_eq_one.mp hcard
  have := tab431_mem
  rw [hT, Finset.mem_singleton] at this
  rw [hT, this]

theorem hatWord_431 : tab431.hatWord = [2, 0, 0, 2, 0, 0, 1, 1] := by
  unfold SkewTableau.hatWord
  have h : TableauRowWord.rowCells yd431 = OddLRExamples.rowCellsOf [4, 3, 1] :=
    OddLRExamples.rowCells_ofRowLens [4, 3, 1] (by decide)
  rw [h]
  decide

/-- `c^{(4,3,1)}_{(2,2),(2,2)} = -1`. -/
theorem oddLR_431_22_22 : oddLR yd431 yd22 yd22 = -1 := by
  rw [OddLRRule.thm_4_8, lrSignedCount, lrTableaux_431, Finset.sum_singleton,
    SkewTableau.sign, SkewTableau.Nlt, hatWord_431]
  decide

/-- The even coefficient `c^{(4,3,1)}_{(2,2),(2,2)}` is `1`. -/
theorem evenLR_431_22_22 : OddLREven.evenLR yd431 yd22 yd22 = 1 := by
  rw [OddLREven.thm_4_1, lrTableaux_431, Finset.card_singleton, Nat.cast_one]

/-- `(2,2,2,2)`. -/
def yd2222 : YoungDiagram := YoungDiagram.ofRowLens [2, 2, 2, 2] (by decide)

/-- `(4,3,1)` strictly dominates `(2,2,2,2)`, the leading shape of `s_{(2,2)}²`. -/
theorem dom_2222_431 : Dom yd2222 yd431 ∧ yd2222 ≠ yd431 := by
  refine ⟨fun k => ?_, fun h => absurd (congrArg (fun μ => decide ((3, 0) ∈ μ)) h) (by decide)⟩
  rcases Nat.lt_or_ge k 8 with hk | hk
  · rw [← card_filter_row_lt, ← card_filter_row_lt]
    interval_cases k <;> decide
  · rw [pre_eq_card (by have : yd2222.card = 8 := by decide
                        omega),
      pre_eq_card (by have : yd431.card = 8 := by decide
                      omega)]
    decide

/-- **Refutation of the printed claim** "for Lima partitions, the odd Littlewood–Richardson
coefficients are equal to the even ones" (for Lima `μ = ν = (2,2)`), and of the non-negativity
of the coefficients `a_μ` in (A.1) (`s_{(2,2)}² = s_{(2,2,2,2)} + ⋯ - s_{(4,3,1)} + ⋯`). -/
theorem printed_oddLR_eq_evenLR_fails :
    IsLima yd22 ∧ oddLR yd431 yd22 yd22 = -1 ∧ OddLREven.evenLR yd431 yd22 yd22 = 1 ∧
      Dom yd2222 yd431 ∧ yd2222 ≠ yd431 :=
  ⟨isLima_yd22, oddLR_431_22_22, evenLR_431_22_22, dom_2222_431⟩

/-! ### Lima Schur functions do not commute -/

theorem cellsL_64321 :
    OddLREven.cellsL yd64321 yd4422 = [(4, 0), (2, 2), (0, 4), (0, 5)] := by
  rw [yd64321, OddLRExamples.cellsL_ofRowLens [6, 4, 3, 2, 1] (by decide)]
  decide

theorem sub_64321 : yd4422.cells ⊆ yd64321.cells := by decide

/-- An LR tableau of shape `(6,4,3,2,1)/(4,4,2,2)` and content `(2,2)`. -/
def tab64321 : SkewTableau yd64321 yd4422 :=
  OddLRExamples.ofWord yd64321 yd4422 _ cellsL_64321 sub_64321 [2, 2, 1, 1] (by decide)

theorem tab64321_mem : tab64321 ∈ lrTableaux yd64321 yd4422 yd22 := by
  rw [mem_lrTableaux]
  constructor
  · ext k
    rw [OddLRRule.skew_content_eq_count, tab64321, OddLRExamples.rowWord_ofWord, shapeContent_22]
  · unfold IsLR
    rw [tab64321, OddLRExamples.rowWord_ofWord]
    exact (OddLRExamples.yamB_iff 2 _ (by decide)).mp (by decide)

theorem lrTableaux_64321 : lrTableaux yd64321 yd4422 yd22 = {tab64321} := by
  have hcard : (lrTableaux yd64321 yd4422 yd22).card = 1 := by
    have := OddLRExamples.card_lrTableaux_eq cellsL_64321 sub_64321 [2, 2] (by decide)
    exact this.trans (by decide)
  obtain ⟨T, hT⟩ := Finset.card_eq_one.mp hcard
  have := tab64321_mem
  rw [hT, Finset.mem_singleton] at this
  rw [hT, this]

theorem oddLR_64321_ne_zero : oddLR yd64321 yd4422 yd22 ≠ 0 := by
  rw [OddLRRule.thm_4_8, lrSignedCount, lrTableaux_64321, Finset.sum_singleton,
    OddLRTableau.SkewTableau.sign, ← pow_add]
  exact pow_ne_zero _ (by norm_num)

theorem eta_64321 : EKLSectionTwo.eta yd64321 = -1 := by
  rw [OddLRMisc.eta_eq_directNorth_north]
  have h1 : TableauStripSigns.directNorth yd64321 = 20 := by decide
  have h2 : TableauStripSigns.north yd64321 = 95 := by decide
  rw [h1, h2]
  norm_num

/-- **Refutation of the printed claim** "Lima Schur functions pairwise commute":
`s_{(4,4,2,2)} s_{(2,2)} ≠ s_{(2,2)} s_{(4,4,2,2)}` in `OΛ`. -/
theorem lima_schur_not_comm : IsLima yd4422 ∧ IsLima yd22 ∧ sK yd4422 * sK yd22 ≠ sK yd22 * sK yd4422 := by
  refine ⟨isLima_yd4422, isLima_yd22, fun h => ?_⟩
  have hr := repr_reverse (sK yd4422 * sK yd22) yd64321
  rw [EKAutomorphisms.reverse_mul, EKLSectionTwo.reverse_sK, EKLSectionTwo.reverse_sK,
    eta_lima isLima_yd4422, eta_lima isLima_yd22, one_smul, one_smul, eta_64321, ← h] at hr
  have : oddLR yd64321 yd4422 yd22 = -oddLR yd64321 yd4422 yd22 := by
    unfold oddLR; rw [neg_eq_neg_one_mul]; exact hr
  exact oddLR_64321_ne_zero (by omega)

end OddMath.Frontier.EQLima

import OddMath.Frontier.OddLREvenExample

/-!
# Yamanouchi examples and the lowest non-Pieri product

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.1, pp. 12–13.

* p. 12: "For example, `312211` is Yamanouchi but `1221` and `112` are not"
  (`yamanouchi_312211`, `not_yamanouchi_1221`, `not_yamanouchi_112`), for the library's
  predicate `OddLRTableau.Yamanouchi` (read backwards, i.e. over all suffixes).
* Example 4.3, p. 13: "The lowest degree product which is not described by the Pieri rule is
  `s₂₁s₂₁`." The Pieri rule (4.3) and its column version describe `s_μ s_ν` when `μ` or `ν` is a
  row `(k)` or a column `(1^k)` (including `k = 0`). Every partition which is neither a row nor a
  column has at least `3` boxes, with equality only for `(2,1)` (`three_le_card`,
  `eq_21_of_card_eq_three`). Hence every product `s_μ s_ν` with `|μ| + |ν| < 6` is a Pieri
  product (`pieri_of_lt_six`), and in degree `6` the only non-Pieri product is `s₂₁s₂₁`
  (`not_pieri_iff_of_eq_six`). The expansion of `s₂₁s₂₁` is `OddLREven.example_4_3`.
-/

namespace OddMath.Frontier.OddLRGaps

open OddLRTableau OddLRExamples

/-! ## Yamanouchi words (E §4.1, p. 12) -/

/-- `312211` is Yamanouchi. -/
theorem yamanouchi_312211 : Yamanouchi [3, 1, 2, 2, 1, 1] :=
  (yamB_iff 3 _ (by decide)).mp (by decide)

/-- `1221` is not Yamanouchi (its suffix `221`). -/
theorem not_yamanouchi_1221 : ¬ Yamanouchi [1, 2, 2, 1] := fun h =>
  absurd ((yamB_iff 2 _ (by decide)).mpr h) (by decide)

/-- `112` is not Yamanouchi (its suffix `2`). -/
theorem not_yamanouchi_112 : ¬ Yamanouchi [1, 1, 2] := fun h =>
  absurd ((yamB_iff 2 _ (by decide)).mpr h) (by decide)

/-! ## Rows, columns and Pieri products (E Example 4.3, p. 13) -/

/-- `μ` is a row `(k)`, `k ≥ 0`. -/
def IsRow (μ : YoungDiagram) : Prop := ∀ p ∈ μ, p.1 = 0

/-- `μ` is a column `(1^k)`, `k ≥ 0`. -/
def IsColumn (μ : YoungDiagram) : Prop := ∀ p ∈ μ, p.2 = 0

/-- `s_μ s_ν` is described by the Pieri rule (4.3) or its column version: `μ` or `ν` is a row
or a column. -/
def IsPieriPair (μ ν : YoungDiagram) : Prop := IsRow μ ∨ IsColumn μ ∨ IsRow ν ∨ IsColumn ν

/-- The three cells of `(2,1)`. -/
def cells21 : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (1, 0)}

theorem cells21_subset {μ : YoungDiagram} (hr : ¬ IsRow μ) (hc : ¬ IsColumn μ) :
    cells21 ⊆ μ.cells := by
  simp only [IsRow, IsColumn, not_forall] at hr hc
  obtain ⟨⟨i, j⟩, hij, hi⟩ := hr
  obtain ⟨⟨k, l⟩, hkl, hl⟩ := hc
  intro p hp
  simp only [cells21, Finset.mem_insert, Finset.mem_singleton] at hp
  rw [YoungDiagram.mem_cells]
  rcases hp with rfl | rfl | rfl
  · exact μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hij
  · exact μ.up_left_mem (Nat.zero_le _) (Nat.one_le_iff_ne_zero.mpr hl) hkl
  · exact μ.up_left_mem (Nat.one_le_iff_ne_zero.mpr hi) (Nat.zero_le _) hij

/-- A partition which is neither a row nor a column has at least three boxes. -/
theorem three_le_card {μ : YoungDiagram} (hr : ¬ IsRow μ) (hc : ¬ IsColumn μ) : 3 ≤ μ.card := by
  have := Finset.card_le_card (cells21_subset hr hc)
  rwa [show cells21.card = 3 by decide] at this

theorem cells_yd21 : (OddLREven.yd [2, 1]).cells = cells21 := by decide

/-- The only such partition with three boxes is `(2,1)`. -/
theorem eq_21_of_card_eq_three {μ : YoungDiagram} (hr : ¬ IsRow μ) (hc : ¬ IsColumn μ)
    (h3 : μ.card = 3) : μ = OddLREven.yd [2, 1] := by
  have hsub := cells21_subset hr hc
  have heq : cells21 = μ.cells :=
    Finset.eq_of_subset_of_card_le hsub (by rw [show cells21.card = 3 by decide]; exact h3.le)
  apply YoungDiagram.ext
  rw [← heq, cells_yd21]

theorem not_isRow_21 : ¬ IsRow (OddLREven.yd [2, 1]) := fun h =>
  absurd (h (1, 0) (by decide)) (by decide)

theorem not_isColumn_21 : ¬ IsColumn (OddLREven.yd [2, 1]) := fun h =>
  absurd (h (0, 1) (by decide)) (by decide)

theorem not_pieri_21 : ¬ IsPieriPair (OddLREven.yd [2, 1]) (OddLREven.yd [2, 1]) := by
  rintro (h | h | h | h)
  · exact not_isRow_21 h
  · exact not_isColumn_21 h
  · exact not_isRow_21 h
  · exact not_isColumn_21 h

/-- E Example 4.3: every product `s_μ s_ν` of degree `|μ| + |ν| < 6` is described by the Pieri
rule. -/
theorem pieri_of_lt_six (μ ν : YoungDiagram) (h : μ.card + ν.card < 6) : IsPieriPair μ ν := by
  by_contra hp
  simp only [IsPieriPair, not_or] at hp
  have := three_le_card hp.1 hp.2.1
  have := three_le_card hp.2.2.1 hp.2.2.2
  omega

/-- E Example 4.3: in degree `6` the only product `s_μ s_ν` not described by the Pieri rule is
`s₂₁s₂₁`. -/
theorem not_pieri_iff_of_eq_six (μ ν : YoungDiagram) (h : μ.card + ν.card = 6) :
    ¬ IsPieriPair μ ν ↔ μ = OddLREven.yd [2, 1] ∧ ν = OddLREven.yd [2, 1] := by
  constructor
  · intro hp
    simp only [IsPieriPair, not_or] at hp
    have h1 := three_le_card hp.1 hp.2.1
    have h2 := three_le_card hp.2.2.1 hp.2.2.2
    exact ⟨eq_21_of_card_eq_three hp.1 hp.2.1 (by omega),
      eq_21_of_card_eq_three hp.2.2.1 hp.2.2.2 (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    exact not_pieri_21

/-- E Example 4.3: `s₂₁s₂₁` is the lowest-degree product not described by the Pieri rule. -/
theorem lowest_non_pieri :
    ¬ IsPieriPair (OddLREven.yd [2, 1]) (OddLREven.yd [2, 1]) ∧
      (OddLREven.yd [2, 1]).card + (OddLREven.yd [2, 1]).card = 6 ∧
      ∀ μ ν : YoungDiagram, ¬ IsPieriPair μ ν → 6 ≤ μ.card + ν.card ∧
        (μ.card + ν.card = 6 → μ = OddLREven.yd [2, 1] ∧ ν = OddLREven.yd [2, 1]) := by
  refine ⟨not_pieri_21, by decide, fun μ ν hp => ⟨?_, fun h6 => (not_pieri_iff_of_eq_six μ ν h6).mp hp⟩⟩
  by_contra hlt
  exact hp (pieri_of_lt_six μ ν (by omega))

end OddMath.Frontier.OddLRGaps

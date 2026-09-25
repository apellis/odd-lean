import OddMath.Frontier.TableauEvaluation

/-!
# Genuine tableau dominance and the normalized signed Kostka coefficient

Ellis arXiv:1111.3932v1 §2.1, (2.6). Rows are zero-based English
coordinates; labels are positive. All fibers and polynomials are the
actual inherited constructions. No Schur equality or basis theorem is claimed.
-/
namespace OddMath.Frontier.TableauDominance

open TableauSign TableauContent TableauRowWord
open scoped BigOperators

variable {μ : YoungDiagram}

noncomputable def shapeContent (μ : YoungDiagram) : ℕ →₀ ℕ :=
  ∑ p ∈ μ.cells, Finsupp.single (p.1 + 1) 1

/-- Row r contains r+1, with the required zeros off the actual shape. -/
def canonicalTableau (μ : YoungDiagram) : PositiveTableau μ where
  entry i j := if (i, j) ∈ μ then i + 1 else 0
  row_weak' hj hp := by
    rw [if_pos hp, if_pos (μ.up_left_mem le_rfl (Nat.le_of_lt hj) hp)]
  col_strict' hi hp := by
    rw [if_pos hp, if_pos (μ.up_left_mem (Nat.le_of_lt hi) le_rfl hp)]
    omega
  zeros' hp := if_neg hp
  positive hp := by simp only [if_pos hp]; omega

@[simp] theorem canonical_entry {p : ℕ × ℕ} (hp : p ∈ μ.cells) :
    (canonicalTableau μ).entry p.1 p.2 = p.1 + 1 := by
  change (if (p.1, p.2) ∈ μ then p.1 + 1 else 0) = p.1 + 1
  exact if_pos (by simpa using hp)

@[simp] theorem content_canonical (μ : YoungDiagram) :
    content (canonicalTableau μ) = shapeContent μ := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  rw [canonical_entry hp]

noncomputable def shapePrefix (μ : YoungDiagram) (k : ℕ) : ℕ :=
  (μ.cells.filter (fun p => p.1 < k)).card

noncomputable def contentPrefix (c : ℕ →₀ ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, c (j + 1)

/-- Positivity and strict columns give this at every cell, not as a premise. -/
theorem entry_ge_row (T : PositiveTableau μ) {i j : ℕ} (hp : (i,j) ∈ μ) :
    i + 1 ≤ T.entry i j := by
  induction i with
  | zero => exact T.positive hp
  | succ i ih =>
    have hp' := μ.up_left_mem (Nat.le_succ i) le_rfl hp
    have h : T.entry i j < T.entry (i+1) j := T.col_strict' (Nat.lt_succ_self i) hp
    have h' : i + 1 ≤ T.entry i j := ih hp'
    change i + 1 + 1 ≤ T.entry (i+1) j
    omega

/-- Multiplicity prefixes count precisely the cells with labels at most k. -/
theorem contentPrefix_eq_card (T : PositiveTableau μ) (k : ℕ) :
    contentPrefix (content T) k =
      (μ.cells.filter (fun p => T.entry p.1 p.2 ≤ k)).card := by
  classical
  unfold contentPrefix
  simp only [content_apply, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpos : 0 < T.entry p.1 p.2 := T.positive (by simpa using hp)
  have he (j : ℕ) : (T.entry p.1 p.2 = j + 1) ↔ j = T.entry p.1 p.2 - 1 := by omega
  simp only [he, Finset.sum_ite_eq', Finset.mem_range]
  by_cases hle : T.entry p.1 p.2 ≤ k
  · rw [if_pos hle, if_pos (show T.entry p.1 p.2 - 1 < k by omega)]
  · rw [if_neg hle, if_neg (show ¬ T.entry p.1 p.2 - 1 < k by omega)]

/-- Every small label lies in the first k rows. -/
theorem prefix_cells_subset (T : PositiveTableau μ) (k : ℕ) :
    μ.cells.filter (fun p => T.entry p.1 p.2 ≤ k) ⊆
      μ.cells.filter (fun p => p.1 < k) := by
  intro p hp
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  have h := entry_ge_row T ((YoungDiagram.mem_cells _).mp hp)
  exact Finset.mem_filter.mpr ⟨hp, by omega⟩

theorem content_dominance (T : PositiveTableau μ) (k : ℕ) :
    contentPrefix (content T) k ≤ shapePrefix μ k := by
  rw [contentPrefix_eq_card]
  exact Finset.card_le_card (prefix_cells_subset T k)

@[simp] theorem shapeContent_prefix (μ : YoungDiagram) (k : ℕ) :
    contentPrefix (shapeContent μ) k = shapePrefix μ k := by
  classical
  rw [← content_canonical, contentPrefix_eq_card]
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [canonical_entry hp]
  omega

theorem fiber_empty_of_prefix (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (h : ∃ k, shapePrefix μ k < contentPrefix c k) :
    tableauxOfContent μ c = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro T hT
  obtain ⟨k, hk⟩ := h
  have hc := content_dominance T k
  rw [(mem_tableauxOfContent T c).mp hT] at hc
  omega

/-- Equal prefix counts turn the inclusion into equality; every cell is forced. -/
theorem eq_canonical_of_content (T : PositiveTableau μ)
    (hc : content T = shapeContent μ) : T = canonicalTableau μ := by
  classical
  apply ext_cells
  intro p hp
  rw [canonical_entry hp]
  have heq : μ.cells.filter (fun q => T.entry q.1 q.2 ≤ p.1 + 1) =
      μ.cells.filter (fun q => q.1 < p.1 + 1) := by
    apply Finset.eq_of_subset_of_card_le (prefix_cells_subset T (p.1+1))
    rw [← contentPrefix_eq_card, hc, shapeContent_prefix]
    exact le_rfl
  have hm : p ∈ μ.cells.filter (fun q => T.entry q.1 q.2 ≤ p.1 + 1) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨hp, by omega⟩
  exact Nat.le_antisymm (Finset.mem_filter.mp hm).2
    (entry_ge_row T ((YoungDiagram.mem_cells _).mp hp))

theorem diagonal_fiber (μ : YoungDiagram) :
    tableauxOfContent μ (shapeContent μ) = {canonicalTableau μ} := by
  classical
  ext T
  simp only [mem_tableauxOfContent, Finset.mem_singleton]
  constructor
  · exact eq_canonical_of_content T
  · intro h; rw [h, content_canonical]

noncomputable def tableauSign (T : PositiveTableau μ) : ℤ :=
  (-1 : ℤ) ^ inversions (rowWord T)

@[simp] theorem tableauSign_mul_self (T : PositiveTableau μ) :
    tableauSign T * tableauSign T = 1 := by
  simp [tableauSign, ← mul_pow]

/-- Source normalization (2.6), not a shape-only LR sign. -/
noncomputable def signedKostka (lam mu : YoungDiagram) : ℤ :=
  tableauSign (canonicalTableau lam) *
    ∑ T ∈ tableauxOfContent lam (shapeContent mu), tableauSign T

@[simp] theorem signedKostka_diag (μ : YoungDiagram) : signedKostka μ μ = 1 := by
  classical
  simp [signedKostka, diagonal_fiber]

theorem signedKostka_zero_of_prefix (lam mu : YoungDiagram)
    (h : ∃ k, shapePrefix lam k < shapePrefix mu k) : signedKostka lam mu = 0 := by
  have hf := fiber_empty_of_prefix lam (shapeContent mu) (by simpa using h)
  simp [signedKostka, hf]

/-- A bounded content shape supplies the literal polynomial's alphabet proof. -/
theorem shapeContent_bounded (n : ℕ) (μ : YoungDiagram)
    (h : ∀ p ∈ μ.cells, p.1 < n) : ∀ k ∈ (shapeContent μ).support, k ≤ n := by
  intro k hk
  rw [← content_canonical, Finsupp.mem_support_iff, content_apply] at hk
  obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hk
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  rw [canonical_entry hp] at he
  have hb := h p hp
  omega

/-- The parent polynomial is a literal tableau sum, not defined by this answer. -/
theorem contentPolynomial_eq_signedKostka (n : ℕ) (lam mu : YoungDiagram)
    (h : ∀ p ∈ mu.cells, p.1 < n) :
    TableauEvaluation.contentPolynomial n lam (shapeContent mu) (shapeContent_bounded n mu h) =
      SkewPolynomial.monomial (fun i : Fin n => shapeContent mu (i.val + 1))
        (((-1 : ℤ) ^ (∑ i : Fin n, i.val * shapeContent mu (i.val + 1))) *
          tableauSign (canonicalTableau lam) * signedKostka lam mu) := by
  classical
  rw [TableauEvaluation.contentPolynomial_eq]
  have he (T : PositiveTableau lam) :
      (-1 : ℤ) ^ LrLegA.totalNorthLt (boxes T) (boxes T) = tableauSign T := by
    rw [tableauSign, rowWord_inversions]
  simp only [he, signedKostka]
  congr 1
  rw [mul_assoc, ← mul_assoc (tableauSign _), tableauSign_mul_self, one_mul]

theorem contentPolynomial_zero_of_prefix (n : ℕ) (lam mu : YoungDiagram)
    (h : ∀ p ∈ mu.cells, p.1 < n)
    (hfail : ∃ k, shapePrefix lam k < shapePrefix mu k) :
    TableauEvaluation.contentPolynomial n lam (shapeContent mu) (shapeContent_bounded n mu h) = 0 := by
  rw [contentPolynomial_eq_signedKostka n lam mu h, signedKostka_zero_of_prefix lam mu hfail]
  simp [SkewPolynomial.monomial]

theorem contentPolynomial_diag (n : ℕ) (μ : YoungDiagram)
    (h : ∀ p ∈ μ.cells, p.1 < n) :
    TableauEvaluation.contentPolynomial n μ (shapeContent μ) (shapeContent_bounded n μ h) =
      SkewPolynomial.monomial (fun i : Fin n => shapeContent μ (i.val + 1))
        (((-1 : ℤ) ^ (∑ i : Fin n, i.val * shapeContent μ (i.val + 1))) *
          tableauSign (canonicalTableau μ)) := by
  rw [contentPolynomial_eq_signedKostka n μ μ h, signedKostka_diag, mul_one]

/-- The signed diagonal coefficient is a unit, even when it is minus one. -/
theorem diagonal_coefficient_sq (n : ℕ) (μ : YoungDiagram) :
    (((( -1 : ℤ) ^ (∑ i : Fin n, i.val * shapeContent μ (i.val + 1))) *
      tableauSign (canonicalTableau μ))) ^ 2 = 1 := by
  rw [mul_pow, pow_two (tableauSign _), tableauSign_mul_self, mul_one,
    ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem diagonal_coefficient_isUnit (n : ℕ) (μ : YoungDiagram) :
    IsUnit (((-1 : ℤ) ^ (∑ i : Fin n, i.val * shapeContent μ (i.val + 1))) *
      tableauSign (canonicalTableau μ)) := by
  have h := diagonal_coefficient_sq n μ
  rw [pow_two] at h
  exact ⟨⟨_, _, h, h⟩, rfl⟩

end OddMath.Frontier.TableauDominance

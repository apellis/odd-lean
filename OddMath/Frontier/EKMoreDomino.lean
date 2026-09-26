import OddMath.Frontier.EKCompleteDomino

/-!
# [EK] §3.3, p. 30: spin and cospin of domino tableaux

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2, §3.3, p. 30: "in order for `λ` to admit a domino tiling, it is necessary
but not sufficient that `|λ|` be even"; "The spin `s(D)` is a non-negative half-integer and the
cospin `s̃(D) = s*(λ) − s(D)` is always an integer."

Tilings are those of `EKComplete` (`IsTiling`: an involution of the cells pairing adjacent
cells), `vert ν σ = 2 s(D)` and `twiceSpinMax ν = 2 s*(ν)`.

* `sum_col_sign_eq`: `Σ_{c ∈ ν} (−1)^{col c} = 2 Σ_{c upper cell of a vertical domino} (−1)^{col c}`
  for every tiling; hence the parity of the number of vertical dominoes is the same for all
  tilings of `ν` (`vert_parity`).
* `ek_p30_cospin_integer`: for every tiling `σ` of `ν`, `2 s*(ν) − 2 s(σ)` is even, i.e. the
  cospin `s*(ν) − s(σ)` is a non-negative integer.
* `ek_p30_even_necessary`: a tileable diagram has an even number of cells
  (via `sum_checker_eq_zero`: equal numbers of black and white cells).
* `ek_p30_even_not_sufficient`: `λ = (3,2,1)` has `6` cells and no domino tiling.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKMore
open EKComplete

variable {ν : YoungDiagram} {σ : ℕ × ℕ → ℕ × ℕ}

/-- Reindexing a sum over the cells by a tiling involution. -/
theorem sum_tiling_comp (hσ : IsTiling ν σ) (f : ℕ × ℕ → ℤ) :
    ∑ c ∈ ν.cells, f (σ c) = ∑ c ∈ ν.cells, f c := by
  apply Finset.sum_nbij' σ σ
  · intro c hc; exact (YoungDiagram.mem_cells _).mpr (hσ.mem c ((YoungDiagram.mem_cells _).mp hc))
  · intro c hc; exact (YoungDiagram.mem_cells _).mpr (hσ.mem c ((YoungDiagram.mem_cells _).mp hc))
  · intro c hc; exact hσ.invol c ((YoungDiagram.mem_cells _).mp hc)
  · intro c hc; exact hσ.invol c ((YoungDiagram.mem_cells _).mp hc)
  · intro c _; rfl

/-- Upper cell of a vertical domino. -/
def IsUp (σ : ℕ × ℕ → ℕ × ℕ) (c : ℕ × ℕ) : Prop := σ c = (c.1 + 1, c.2)
/-- Lower cell of a vertical domino. -/
def IsDown (σ : ℕ × ℕ → ℕ × ℕ) (c : ℕ × ℕ) : Prop := c.1 = (σ c).1 + 1 ∧ c.2 = (σ c).2

instance (c : ℕ × ℕ) : Decidable (IsUp σ c) := inferInstanceAs (Decidable (_ = _))
instance (c : ℕ × ℕ) : Decidable (IsDown σ c) := inferInstanceAs (Decidable (_ ∧ _))

def colSign (c : ℕ × ℕ) : ℤ := (-1) ^ c.2
def checker (c : ℕ × ℕ) : ℤ := (-1) ^ (c.1 + c.2)

theorem pointwise_col (hσ : IsTiling ν σ) {c : ℕ × ℕ} (hc : c ∈ ν) :
    colSign c + colSign (σ c) =
      2 * ((if IsUp σ c then colSign c else 0) + (if IsDown σ c then colSign c else 0)) := by
  rcases hσ.adj c hc with h | h | h | h
  · have hu : IsUp σ c := h
    have hd : ¬ IsDown σ c := by unfold IsDown; rw [h]; omega
    rw [if_pos hu, if_neg hd, h, colSign, colSign]; ring
  · have hu : ¬ IsUp σ c := by unfold IsUp; rw [h]; simp
    have hd : ¬ IsDown σ c := by unfold IsDown; rw [h]; simp
    rw [if_neg hu, if_neg hd, h, colSign, colSign, pow_succ]; ring
  · have hu : ¬ IsUp σ c := by unfold IsUp; intro h'; rw [h'] at h; dsimp only at h; omega
    have hd : IsDown σ c := h
    rw [if_neg hu, if_pos hd, colSign, colSign, ← h.2]; ring
  · have hu : ¬ IsUp σ c := by unfold IsUp; intro h'; rw [h'] at h; dsimp only at h; omega
    have hd : ¬ IsDown σ c := by unfold IsDown; omega
    rw [if_neg hu, if_neg hd, colSign, colSign, h.2, pow_succ]; ring

theorem pointwise_checker (hσ : IsTiling ν σ) {c : ℕ × ℕ} (hc : c ∈ ν) :
    checker c + checker (σ c) = 0 := by
  rcases hσ.adj c hc with h | h | h | h
  · rw [checker, checker, h, show c.1 + 1 + c.2 = c.1 + c.2 + 1 by omega, pow_succ]; ring
  · rw [checker, checker, h, ← add_assoc, pow_succ]; ring
  · rw [checker, checker, h.1, h.2, show (σ c).1 + 1 + (σ c).2 = (σ c).1 + (σ c).2 + 1 by omega,
      pow_succ]; ring
  · rw [checker, checker, h.1, h.2, ← add_assoc, pow_succ]; ring

/-- Black and white cells are equinumerous in a tileable diagram. -/
theorem sum_checker_eq_zero (hσ : IsTiling ν σ) : ∑ c ∈ ν.cells, checker c = 0 := by
  have h2 : ∑ c ∈ ν.cells, (checker c + checker (σ c)) = 0 :=
    Finset.sum_eq_zero fun c hc => pointwise_checker hσ ((YoungDiagram.mem_cells _).mp hc)
  rw [Finset.sum_add_distrib, sum_tiling_comp hσ checker] at h2
  omega

theorem sum_down_eq_sum_up (hσ : IsTiling ν σ) :
    ∑ c ∈ ν.cells, (if IsDown σ c then colSign c else 0) =
      ∑ c ∈ ν.cells, (if IsUp σ c then colSign c else 0) := by
  rw [← sum_tiling_comp hσ]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := (YoungDiagram.mem_cells _).mp hc
  have hinv := hσ.invol c hc'
  by_cases hu : IsUp σ c
  · have hd : IsDown σ (σ c) := by unfold IsDown; rw [hinv, hu]; simp
    rw [if_pos hd, if_pos hu, colSign, colSign, hu]
  · have hd : ¬ IsDown σ (σ c) := by
      unfold IsDown; rw [hinv]; intro h; apply hu; unfold IsUp
      exact Prod.ext (by simpa using h.1) (by simpa using h.2)
    rw [if_neg hd, if_neg hu]

/-- `Σ_ν (−1)^{col} = 2 Σ_{upper vertical cells} (−1)^{col}`. -/
theorem sum_col_sign_eq (hσ : IsTiling ν σ) :
    ∑ c ∈ ν.cells, colSign c = 2 * ∑ c ∈ ν.cells, (if IsUp σ c then colSign c else 0) := by
  have h2 : ∑ c ∈ ν.cells, (colSign c + colSign (σ c)) =
      ∑ c ∈ ν.cells, 2 * ((if IsUp σ c then colSign c else 0) +
        (if IsDown σ c then colSign c else 0)) :=
    Finset.sum_congr rfl fun c hc => pointwise_col hσ ((YoungDiagram.mem_cells _).mp hc)
  rw [Finset.sum_add_distrib, sum_tiling_comp hσ colSign, ← Finset.mul_sum,
    Finset.sum_add_distrib, sum_down_eq_sum_up hσ] at h2
  linarith

theorem sum_sign_parity (s : Finset (ℕ × ℕ)) (p : ℕ × ℕ → Prop) [DecidablePred p] :
    ∃ m : ℤ, ∑ c ∈ s, (if p c then colSign c else 0) = ((s.filter p).card : ℤ) + 2 * m := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨m, hm⟩ := ih
    rw [Finset.sum_insert ha, hm, Finset.filter_insert]
    by_cases hp : p a
    · rw [if_pos hp, if_pos hp, Finset.card_insert_of_not_mem (fun h => ha (Finset.mem_filter.mp h).1)]
      rcases neg_one_pow_eq_or ℤ a.2 with h | h
      · exact ⟨m, by rw [colSign, h]; push_cast; ring⟩
      · exact ⟨m - 1, by rw [colSign, h]; push_cast; ring⟩
    · rw [if_neg hp, if_neg hp]; exact ⟨m, by ring⟩

theorem vert_eq_filter (σ : ℕ × ℕ → ℕ × ℕ) : vert ν σ = (ν.cells.filter (IsUp σ)).card := rfl

/-- The parity of the number of vertical dominoes does not depend on the tiling. -/
theorem vert_parity {τ : ℕ × ℕ → ℕ × ℕ} (hσ : IsTiling ν σ) (hτ : IsTiling ν τ) :
    vert ν σ % 2 = vert ν τ % 2 := by
  have h1 := sum_col_sign_eq hσ
  have h2 := sum_col_sign_eq hτ
  obtain ⟨m, hm⟩ := sum_sign_parity ν.cells (IsUp σ)
  obtain ⟨m', hm'⟩ := sum_sign_parity ν.cells (IsUp τ)
  rw [vert_eq_filter, vert_eq_filter]
  omega

/-- [EK] p. 30: the cospin is always an integer: `2 s*(ν) − 2 s(σ)` is even and non-negative for
every domino tiling `σ` of `ν`. -/
theorem ek_p30_cospin_integer (hσ : IsTiling ν σ) :
    ∃ c : ℕ, twiceSpinMax ν = vert ν σ + 2 * c := by
  have hb : BddAbove {v | ∃ τ, IsTiling ν τ ∧ v = vert ν τ} :=
    ⟨_, fun v ⟨τ, hτ, hv⟩ => hv ▸ vert_le ν hτ⟩
  have hne : ({v | ∃ τ, IsTiling ν τ ∧ v = vert ν τ} : Set ℕ).Nonempty := ⟨_, σ, hσ, rfl⟩
  obtain ⟨τ, hτ, hmax⟩ := Nat.sSup_mem hne hb
  have hle : vert ν σ ≤ twiceSpinMax ν := le_csSup hb ⟨σ, hσ, rfl⟩
  have hp := vert_parity hσ hτ
  rw [twiceSpinMax, hmax] at hle ⊢
  exact ⟨(vert ν τ - vert ν σ) / 2, by omega⟩

theorem sum_checker_parity (s : Finset (ℕ × ℕ)) :
    ∃ m : ℤ, ∑ c ∈ s, checker c = (s.card : ℤ) + 2 * m := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨m, hm⟩ := ih
    rw [Finset.sum_insert ha, hm, Finset.card_insert_of_not_mem ha]
    rcases neg_one_pow_eq_or ℤ (a.1 + a.2) with h | h
    · exact ⟨m, by rw [checker, h]; push_cast; ring⟩
    · exact ⟨m - 1, by rw [checker, h]; push_cast; ring⟩

/-- [EK] p. 30: a diagram admitting a domino tiling has an even number of cells. -/
theorem ek_p30_even_necessary (hσ : IsTiling ν σ) : Even ν.card := by
  obtain ⟨m, hm⟩ := sum_checker_parity ν.cells
  rw [sum_checker_eq_zero hσ] at hm
  have : (ν.card : ℤ) = 2 * (-m) := by rw [YoungDiagram.card]; linarith
  exact ⟨(-m).toNat, by omega⟩

/-- The staircase `(3,2,1)`. -/
def staircase321 : YoungDiagram := YoungDiagram.ofRowLens [3, 2, 1] (by decide)

theorem staircase321_card : staircase321.card = 6 := by
  rw [staircase321, EKPartitionSpanning.card_ofRowLens]; rfl

theorem staircase321_checker : ∑ c ∈ staircase321.cells, checker c = 2 := by
  have hc : staircase321.cells = {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)} := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, staircase321, YoungDiagram.mem_ofRowLens,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hi, hj⟩
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp at hj <;> omega
    · rintro (h | h | h | h | h | h) <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨by simp, by simp⟩
  rw [hc]
  decide

/-- [EK] p. 30: `|λ|` even is not sufficient for a domino tiling: `(3,2,1)` has `6` cells and
no domino tiling. -/
theorem ek_p30_even_not_sufficient :
    Even staircase321.card ∧ ¬ ∃ σ, IsTiling staircase321 σ := by
  refine ⟨by rw [staircase321_card]; decide, fun ⟨σ, hσ⟩ => ?_⟩
  have := sum_checker_eq_zero hσ
  rw [staircase321_checker] at this
  norm_num at this

end OddMath.Frontier.EKMore

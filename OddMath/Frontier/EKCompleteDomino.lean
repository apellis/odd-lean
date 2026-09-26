import OddMath.Frontier.EKCompleteLemma215

/-!
# [EK] p. 31: the norm of an odd Schur function via domino tilings of `2λ`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §3.3, p. 31. A domino tiling of a diagram is a
tiling by `2 × 1` dominoes; its spin `s(D)` is one half of the number of vertical dominoes,
`s*(λ)` is the largest spin of a tiling of `λ`, and the paper states
`⟨s_λ, s_λ⟩ = (−1)^{½ s*(2λ)}`.

* With `2λ = (2λ₁, 2λ₂, …)`, `s*(2λ) = Σ_j ⌊λᵀ_j / 2⌋` (`twiceSpinMax_double`), an integer, and
  `½ s*(2λ)` need not be one: for `λ = (1,1)`, `s*(2λ) = 1` (`printed_exponent_not_integer`).
* The formula that holds, for every `λ`, is `⟨s_λ, s_λ⟩ = (−1)^{s*(2λ)}` (`norm_schur_spin`),
  from Cor 3.9 and `C(c,2) ≡ ⌊c/2⌋ (mod 2)`.

A tiling of a diagram `ν` is modelled as an involution `σ` of its cells with `σ(c)` adjacent to
`c` (the partner cell in the domino covering `c`); `vert σ` counts the upper cells of vertical
dominoes, so `s(D) = vert σ / 2`. `twiceSpinMax ν = 2 s*(ν)` is the largest `vert σ`.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKComplete
open EKRadicalQuotient EKIntegralBases DegreeShapes

/-! ## Domino tilings -/

/-- `σ` pairs every cell of `ν` with an adjacent cell of `ν`: a domino tiling of `ν`. -/
structure IsTiling (ν : YoungDiagram) (σ : ℕ × ℕ → ℕ × ℕ) : Prop where
  mem : ∀ c ∈ ν, σ c ∈ ν
  invol : ∀ c ∈ ν, σ (σ c) = c
  adj : ∀ c ∈ ν, σ c = (c.1 + 1, c.2) ∨ σ c = (c.1, c.2 + 1) ∨
    (c.1 = (σ c).1 + 1 ∧ c.2 = (σ c).2) ∨ (c.1 = (σ c).1 ∧ c.2 = (σ c).2 + 1)

/-- The number of vertical dominoes (counted by their upper cell): `2 s(D)`. -/
def vert (ν : YoungDiagram) (σ : ℕ × ℕ → ℕ × ℕ) : ℕ :=
  (ν.cells.filter fun c => σ c = (c.1 + 1, c.2)).card

/-- `2 s*(ν)`: the largest number of vertical dominoes in a domino tiling of `ν`. -/
def twiceSpinMax (ν : YoungDiagram) : ℕ :=
  sSup {v | ∃ σ, IsTiling ν σ ∧ v = vert ν σ}

/-! ## Upper bound: at most `⌊colLen_j / 2⌋` vertical dominoes in column `j` -/

theorem vert_col_le (ν : YoungDiagram) {σ : ℕ × ℕ → ℕ × ℕ} (hσ : IsTiling ν σ) (j : ℕ) :
    2 * ((ν.cells.filter fun c => σ c = (c.1 + 1, c.2)).filter fun c => c.2 = j).card ≤
      ν.colLen j := by
  classical
  have hF : ∀ c, c ∈ ((ν.cells.filter fun c => σ c = (c.1 + 1, c.2)).filter fun c => c.2 = j) ↔
      (c ∈ ν ∧ σ c = (c.1 + 1, c.2)) ∧ c.2 = j := by
    intro c; simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  generalize hFdef : ((ν.cells.filter fun c => σ c = (c.1 + 1, c.2)).filter fun c => c.2 = j) = F
    at hF ⊢
  have hG : (F.image fun c => (c.1 + 1, c.2)).card = F.card := Finset.card_image_of_injective _ (by
    intro a b h; simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) h.2)
  have hsub : F ∪ F.image (fun c => (c.1 + 1, c.2)) ⊆ ν.col j := by
    intro c hc
    rw [YoungDiagram.mem_col_iff]
    rcases Finset.mem_union.mp hc with h | h
    · have h' := (hF c).mp h
      exact ⟨h'.1.1, h'.2⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      have ha' := (hF a).mp ha
      have := hσ.mem a ha'.1.1
      rw [ha'.1.2] at this
      exact ⟨this, ha'.2⟩
  have hdisj : Disjoint F (F.image fun c => (c.1 + 1, c.2)) := by
    rw [Finset.disjoint_left]
    intro c hcF hcG
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcG
    have ha' := (hF a).mp ha
    have hc' := (hF _).mp hcF
    have h1 := hσ.invol a ha'.1.1
    rw [ha'.1.2, hc'.1.2] at h1
    have h2 := congrArg Prod.fst h1
    dsimp only at h2
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hG, ← YoungDiagram.colLen_eq_card] at this
  omega

theorem vert_le (ν : YoungDiagram) {σ : ℕ × ℕ → ℕ × ℕ} (hσ : IsTiling ν σ) :
    vert ν σ ≤ ∑ j ∈ Finset.range (ν.rowLen 0), ν.colLen j / 2 := by
  classical
  rw [vert, Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.range (ν.rowLen 0))]
  · refine Finset.sum_le_sum fun j _ => ?_
    have := vert_col_le ν hσ j
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    linarith
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hc
    rw [Finset.mem_coe, Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
    exact ν.up_left_mem (Nat.zero_le _) le_rfl hc.1

/-! ## The diagram `2λ` -/

/-- `2λ = (2λ₁, 2λ₂, …)`. -/
def double (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.biUnion fun c => {(c.1, 2 * c.2), (c.1, 2 * c.2 + 1)}
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at ha ⊢
    obtain ⟨c, hc, hac⟩ := ha
    refine ⟨(b.1, b.2 / 2), ?_, ?_⟩
    · have hle : (b.1, b.2 / 2) ≤ c := by
        rcases hac with rfl | rfl
        · exact ⟨hba.1, by have := hba.2; simp at this ⊢; omega⟩
        · exact ⟨hba.1, by have := hba.2; simp at this ⊢; omega⟩
      exact μ.isLowerSet hle hc
    · rcases Nat.even_or_odd b.2 with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact Or.inl (Prod.ext rfl (by dsimp only; omega))
      · exact Or.inr (Prod.ext rfl (by dsimp only; omega))

theorem mem_double (μ : YoungDiagram) (i j : ℕ) : (i, j) ∈ double μ ↔ (i, j / 2) ∈ μ := by
  change (i, j) ∈ (double μ).cells ↔ _
  simp only [double, Finset.mem_biUnion, YoungDiagram.mem_cells, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simpa using hc
    · have : (2 * c.2 + 1) / 2 = c.2 := by omega
      simpa [this] using hc
  · intro h
    refine ⟨(i, j / 2), h, ?_⟩
    rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; omega
    · right; omega

/-- `2λ` has row lengths `2λ_i`. -/
theorem double_rowLen (μ : YoungDiagram) (i : ℕ) : (double μ).rowLen i = 2 * μ.rowLen i := by
  apply le_antisymm
  · by_contra h
    have h1 : (i, 2 * μ.rowLen i) ∈ double μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [mem_double, YoungDiagram.mem_iff_lt_rowLen] at h1
    omega
  · by_contra h
    have h1 : (i, (double μ).rowLen i) ∉ double μ := fun hm =>
      lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)
    rw [mem_double, YoungDiagram.mem_iff_lt_rowLen] at h1
    omega

theorem double_colLen (μ : YoungDiagram) (j : ℕ) : (double μ).colLen j = μ.colLen (j / 2) := by
  apply le_antisymm
  · by_contra h
    have h1 : (μ.colLen (j / 2), j) ∈ double μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [mem_double, YoungDiagram.mem_iff_lt_colLen] at h1
    omega
  · by_contra h
    have h1 : ((double μ).colLen j, j) ∉ double μ := fun hm =>
      lt_irrefl _ (YoungDiagram.mem_iff_lt_colLen.mp hm)
    rw [mem_double, YoungDiagram.mem_iff_lt_colLen] at h1
    omega

theorem sum_range_double (g : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), g (j / 2) = 2 * ∑ t ∈ Finset.range m, g t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega]
    ring

/-- The bound for `2λ`: `Σ_j ⌊(2λ)ᵀ_j/2⌋ = 2 Σ_t ⌊λᵀ_t/2⌋`. -/
def colBound (μ : YoungDiagram) : ℕ := ∑ t ∈ Finset.range (μ.rowLen 0), μ.colLen t / 2

theorem double_bound (μ : YoungDiagram) :
    ∑ j ∈ Finset.range ((double μ).rowLen 0), (double μ).colLen j / 2 = 2 * colBound μ := by
  rw [double_rowLen]
  simp only [double_colLen]
  exact sum_range_double (fun t => μ.colLen t / 2) _

/-! ## A tiling of `2λ` attaining the bound -/

/-- Column pair `2t, 2t+1` of `2λ` has height `c = λᵀ_t`: vertical dominoes in rows
`(2r, 2r+1)`, `2r + 1 < c`, and one horizontal domino in row `c − 1` if `c` is odd. -/
def stdTiling (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ × ℕ :=
  if c.1 < 2 * (μ.colLen (c.2 / 2) / 2) then
    (if c.1 % 2 = 0 then (c.1 + 1, c.2) else (c.1 - 1, c.2))
  else (if c.2 % 2 = 0 then (c.1, c.2 + 1) else (c.1, c.2 - 1))

theorem std_v0 {μ : YoungDiagram} {i j : ℕ} (h1 : i < 2 * (μ.colLen (j / 2) / 2))
    (h2 : i % 2 = 0) : stdTiling μ (i, j) = (i + 1, j) := by
  simp [stdTiling, h1, h2]

theorem std_v1 {μ : YoungDiagram} {i j : ℕ} (h1 : i < 2 * (μ.colLen (j / 2) / 2))
    (h2 : i % 2 ≠ 0) : stdTiling μ (i, j) = (i - 1, j) := by
  simp [stdTiling, h1, h2]

theorem std_h0 {μ : YoungDiagram} {i j : ℕ} (h1 : ¬ i < 2 * (μ.colLen (j / 2) / 2))
    (h2 : j % 2 = 0) : stdTiling μ (i, j) = (i, j + 1) := by
  simp [stdTiling, h1, h2]

theorem std_h1 {μ : YoungDiagram} {i j : ℕ} (h1 : ¬ i < 2 * (μ.colLen (j / 2) / 2))
    (h2 : j % 2 ≠ 0) : stdTiling μ (i, j) = (i, j - 1) := by
  simp [stdTiling, h1, h2]

theorem stdTiling_isTiling (μ : YoungDiagram) : IsTiling (double μ) (stdTiling μ) := by
  have hmem : ∀ i j : ℕ, (i, j) ∈ double μ ↔ i < μ.colLen (j / 2) := fun i j => by
    rw [mem_double, YoungDiagram.mem_iff_lt_colLen]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ hc
    rw [hmem] at hc
    by_cases h1 : i < 2 * (μ.colLen (j / 2) / 2)
    · by_cases h2 : i % 2 = 0
      · rw [std_v0 h1 h2, hmem]; omega
      · rw [std_v1 h1 h2, hmem]; omega
    · by_cases h2 : j % 2 = 0
      · rw [std_h0 h1 h2, hmem, show (j + 1) / 2 = j / 2 by omega]; exact hc
      · rw [std_h1 h1 h2, hmem, show (j - 1) / 2 = j / 2 by omega]; exact hc
  · rintro ⟨i, j⟩ hc
    rw [hmem] at hc
    by_cases h1 : i < 2 * (μ.colLen (j / 2) / 2)
    · by_cases h2 : i % 2 = 0
      · rw [std_v0 h1 h2, std_v1 (by omega) (by omega)]; rfl
      · rw [std_v1 h1 h2, std_v0 (by omega) (by omega)]
        exact Prod.ext (by dsimp only; omega) rfl
    · by_cases h2 : j % 2 = 0
      · have he : (j + 1) / 2 = j / 2 := by omega
        rw [std_h0 h1 h2, std_h1 (by rw [he]; exact h1) (by omega)]; rfl
      · have he : (j - 1) / 2 = j / 2 := by omega
        rw [std_h1 h1 h2, std_h0 (by rw [he]; exact h1) (by omega)]
        exact Prod.ext rfl (by dsimp only; omega)
  · rintro ⟨i, j⟩ _
    by_cases h1 : i < 2 * (μ.colLen (j / 2) / 2)
    · by_cases h2 : i % 2 = 0
      · rw [std_v0 h1 h2]; exact Or.inl rfl
      · rw [std_v1 h1 h2]; exact Or.inr (Or.inr (Or.inl ⟨by dsimp only; omega, rfl⟩))
    · by_cases h2 : j % 2 = 0
      · rw [std_h0 h1 h2]; exact Or.inr (Or.inl rfl)
      · rw [std_h1 h1 h2]; exact Or.inr (Or.inr (Or.inr ⟨rfl, by dsimp only; omega⟩))

theorem stdTiling_vert (μ : YoungDiagram) : 2 * colBound μ ≤ vert (double μ) (stdTiling μ) := by
  classical
  rw [← double_bound, vert]
  set S := (Finset.range ((double μ).rowLen 0)).sigma
    fun j => Finset.range ((double μ).colLen j / 2)
  have hS : S.card = ∑ j ∈ Finset.range ((double μ).rowLen 0), (double μ).colLen j / 2 := by
    simp [S, Finset.card_sigma]
  rw [← hS]
  refine Finset.card_le_card_of_injOn (fun p => (2 * p.2, p.1)) ?_ ?_
  · rintro ⟨j, r⟩ hp
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range, double_colLen] at hp
    rw [Finset.mem_filter, YoungDiagram.mem_cells]
    refine ⟨?_, ?_⟩
    · rw [mem_double, YoungDiagram.mem_iff_lt_colLen]; omega
    · exact std_v0 (by omega) (by omega)
  · rintro ⟨j, r⟩ _ ⟨j', r'⟩ _ h
    simp only [Prod.mk.injEq] at h
    have h1 : r = r' := by omega
    subst h1; rw [h.2]

/-- `2 s*(2λ) = 2 Σ_t ⌊λᵀ_t/2⌋`, i.e. `s*(2λ) = Σ_t ⌊λᵀ_t / 2⌋`. -/
theorem twiceSpinMax_double (μ : YoungDiagram) : twiceSpinMax (double μ) = 2 * colBound μ := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨stdTiling μ, stdTiling_isTiling μ, ?_⟩, ?_⟩
  · apply le_antisymm (stdTiling_vert μ)
    rw [← double_bound]; exact vert_le _ (stdTiling_isTiling μ)
  · rintro v ⟨σ, hσ, rfl⟩
    rw [← double_bound]; exact vert_le _ hσ

/-! ## The norm formula -/

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

theorem neg_one_pow_choose_two (c : ℕ) : (-1 : ℤ) ^ (c.choose 2) = (-1 : ℤ) ^ (c / 2) := by
  have key : ∀ c : ℕ, Even (c.choose 2 + c / 2) := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      match c with
      | 0 => exact ⟨0, rfl⟩
      | 1 => exact ⟨0, rfl⟩
      | 2 => exact ⟨1, rfl⟩
      | 3 => exact ⟨2, rfl⟩
      | c + 4 =>
        have h := ih c (by omega)
        have e1 : (c + 4).choose 2 = (c + 3) + (c + 3).choose 2 := choose_two_succ (c + 3)
        have e2 : (c + 3).choose 2 = (c + 2) + (c + 2).choose 2 := choose_two_succ (c + 2)
        have e3 : (c + 2).choose 2 = (c + 1) + (c + 1).choose 2 := choose_two_succ (c + 1)
        have e4 : (c + 1).choose 2 = c + c.choose 2 := choose_two_succ c
        have hs : (c + 4).choose 2 + (c + 4) / 2 = (c.choose 2 + c / 2) + 2 * (2 * c + 4) := by
          omega
        rw [hs]
        exact h.add (even_two_mul _)
  have he : Even (c.choose 2 + c / 2) := key c
  have h1 : (-1 : ℤ) ^ (c.choose 2) * (-1 : ℤ) ^ (c / 2) = 1 := by
    rw [← pow_add, he.neg_one_pow]
  have h2 : (-1 : ℤ) ^ (c / 2) * (-1 : ℤ) ^ (c / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-1 : ℤ) ^ (c / 2) * h1 - (-1 : ℤ) ^ (c.choose 2) * h2

theorem transposeChoose_eq (μ : YoungDiagram) :
    EKSchurOrthonormalControls.transposeChoose μ =
      ∑ t ∈ Finset.range (μ.rowLen 0), (μ.colLen t).choose 2 := by
  have hr : μ.transpose.rowLens = (List.range (μ.rowLen 0)).map μ.colLen := by
    unfold YoungDiagram.rowLens
    rw [YoungDiagram.colLen_transpose]
    congr 1
    funext t
    exact YoungDiagram.rowLen_transpose μ t
  unfold EKSchurOrthonormalControls.transposeChoose
  rw [hr, List.map_map]
  rfl

/-- **p. 31, corrected**: `⟨s_λ, s_λ⟩ = (−1)^{s*(2λ)}` for every `λ`, where
`s*(2λ) = twiceSpinMax (2λ) / 2`. -/
theorem norm_schur_spin (d : ℕ) (lam : DegreeShape d) :
    quotientPairing (EKSchurOrthonormal.schur d lam : Q) (EKSchurOrthonormal.schur d lam : Q) =
      (-1 : ℤ) ^ (twiceSpinMax (double lam.val) / 2) := by
  rw [EKClosureComposition.corollary_3_9, if_pos rfl, twiceSpinMax_double,
    Nat.mul_div_cancel_left _ (by norm_num), transposeChoose_eq, colBound,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun t _ => neg_one_pow_choose_two _

/-- **p. 31, printed exponent**: for `λ = (1,1)`, `s*(2λ) = 1`, so `½ s*(2λ) = ½` is not an
integer and `(−1)^{½ s*(2λ)}` is undefined as an integer power. -/
theorem printed_exponent_not_integer (lam : YoungDiagram) (hl : lam.rowLens = [1, 1]) :
    twiceSpinMax (double lam) = 2 ∧ ¬ ∃ n : ℤ, ((twiceSpinMax (double lam) : ℚ) / 2) / 2 = n := by
  have hc : lam.colLen 0 = 2 := by rw [← YoungDiagram.length_rowLens, hl]; rfl
  have hr : lam.rowLen 0 = 1 := by
    have h0 : 0 < lam.rowLens.length := by rw [hl]; decide
    rw [← YoungDiagram.get_rowLens (h := h0)]
    simp [hl]
  have h2 : twiceSpinMax (double lam) = 2 := by
    rw [twiceSpinMax_double, colBound, hr]
    simp [hc]
  refine ⟨h2, ?_⟩
  rintro ⟨n, hn⟩
  rw [h2] at hn
  have h3 : (2 : ℚ) * n = 1 := by rw [← hn]; norm_num
  have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
  omega

end OddMath.Frontier.EKComplete

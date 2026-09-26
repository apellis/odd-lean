import OddMath.Frontier.EKGeneralQ

/-!
# The maximal crossing number of a margin matrix

Combinatorial input for the degree and leading coefficient of the Gram determinant of the form
(2.1) at unspecialised `q` (Ellis–Khovanov, arXiv:1107.5610v2, §1.2 p.3 "nondegenerate over
`ℚ(q)`" and §5.2 p.40, (5.1)–(5.2)).

For a matrix `M` of naturals with row sums `β` and column sums `α` (both summing to `n`),
`crossing M` is the number of crossings of the corresponding double-coset diagram
(`EKGeneralQ.sourceForm_eq_matForm`).  With `T'(γ) = n² - Σ γᵢ²` (twice the number of pairs of
strands in different platforms):

* `crossing_identity`: `2n² - Σβᵢ² - Σαⱼ² = 4·crossing M + defect M`, where `defect M ≥ 0`
  counts pairs of nonzero cells sharing a row or a column, and (twice) nested pairs;
* `four_crossing_le`: `4·crossing M ≤ T'(β) + T'(α)`;
* `eq_antidiag_of_defect_eq_zero`: if all parts are positive and equality holds, then
  `β` and `α` have the same length, `αⱼ = β_{r-1-j}`, and `M` is the antidiagonal matrix;
* `defect_antidiag`: conversely the antidiagonal matrix attains equality.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKPairingMatrices

variable {r c : ℕ}

/-- Weight of an ordered pair of cells `(i,j)`, `(k,l)` in the defect. -/
def cellWeight (i k : Fin r) (j l : Fin c) : ℕ :=
  (if i = k ∧ j ≠ l then 1 else 0) + (if j = l ∧ i ≠ k then 1 else 0) +
  (if i < k ∧ j < l then 2 else 0) + (if k < i ∧ l < j then 2 else 0)

/-- Pairs of nonzero cells in a common row or column, and (twice) nested pairs. -/
def defect (M : Raw r c) : ℕ :=
  ∑ i, ∑ j, ∑ k, ∑ l, M i j * M k l * cellWeight i k j l

/-- `Σ vᵢ²`. -/
def sqSum {m : ℕ} (v : Fin m → ℕ) : ℤ := ∑ i, ((v i : ℤ)) ^ 2

private theorem sum_sq_eq (M : Raw r c) :
    ((∑ i, ∑ j, M i j : ℕ) : ℤ) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, ((M i j : ℤ) * M k l) := by
  push_cast
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.mul_sum]

private theorem sqSum_row (M : Raw r c) :
    sqSum (rowSum M) = ∑ i, ∑ j, ∑ k, ∑ l, (if i = k then (M i j : ℤ) * M k l else 0) := by
  unfold sqSum rowSum
  apply Finset.sum_congr rfl; intro i _
  push_cast
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

private theorem sqSum_col (M : Raw r c) :
    sqSum (colSum M) = ∑ i, ∑ j, ∑ k, ∑ l, (if j = l then (M i j : ℤ) * M k l else 0) := by
  have h : ∀ i j k, (∑ l, if j = l then (M i j : ℤ) * M k l else 0) = (M i j : ℤ) * M k j := by
    intro i j k
    simp
  simp only [h]
  unfold sqSum colSum
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  push_cast
  rw [sq, Finset.sum_mul_sum]

private theorem crossing_cast (M : Raw r c) :
    (crossing M : ℤ) = ∑ i, ∑ j, ∑ k, ∑ l,
      (if i < k ∧ l < j then (M i j : ℤ) * M k l else 0) := by
  rw [crossing_expanded]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

private theorem sum4_swap (G : Fin r → Fin c → Fin r → Fin c → ℤ) :
    ∑ i, ∑ j, ∑ k, ∑ l, G i j k l = ∑ i, ∑ j, ∑ k, ∑ l, G k l i j := by
  calc ∑ i, ∑ j, ∑ k, ∑ l, G i j k l
        = ∑ x : Fin r × Fin c, ∑ y : Fin r × Fin c, G x.1 x.2 y.1 y.2 := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ y : Fin r × Fin c, ∑ x : Fin r × Fin c, G x.1 x.2 y.1 y.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem crossing_cast' (M : Raw r c) :
    (crossing M : ℤ) = ∑ i, ∑ j, ∑ k, ∑ l,
      (if k < i ∧ j < l then (M i j : ℤ) * M k l else 0) := by
  rw [crossing_cast, sum4_swap]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  rw [mul_comm]

private theorem defect_cast (M : Raw r c) :
    (defect M : ℤ) = ∑ i, ∑ j, ∑ k, ∑ l, ((M i j : ℤ) * M k l) * (cellWeight i k j l : ℤ) := by
  unfold defect
  push_cast
  rfl

private theorem weight_identity (i k : Fin r) (j l : Fin c) (x : ℤ) :
    2 * x - (if i = k then x else 0) - (if j = l then x else 0) =
      2 * (if i < k ∧ l < j then x else 0) + 2 * (if k < i ∧ j < l then x else 0) +
        x * (cellWeight i k j l : ℤ) := by
  unfold cellWeight
  rcases lt_trichotomy i k with hik | hik | hik <;>
  rcases lt_trichotomy j l with hjl | hjl | hjl
  all_goals
    simp only [hik, hjl, lt_irrefl, ne_eq, not_true_eq_false, not_false_eq_true, and_true,
      and_false, true_and, false_and, if_true, if_false, ne_of_lt, ne_of_gt,
      not_lt_of_gt, lt_asymm, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  all_goals ring

/-- `2n² - Σβᵢ² - Σαⱼ² = 4·crossing + defect`. -/
theorem crossing_identity (M : Raw r c) :
    2 * ((∑ i, ∑ j, M i j : ℕ) : ℤ) ^ 2 - sqSum (rowSum M) - sqSum (colSum M) =
      4 * (crossing M : ℤ) + defect M := by
  rw [sum_sq_eq, sqSum_row, sqSum_col, defect_cast]
  have h4 : 4 * (crossing M : ℤ) = 2 * (crossing M : ℤ) + 2 * (crossing M : ℤ) := by ring
  rw [h4]
  nth_rewrite 1 [crossing_cast]
  rw [crossing_cast']
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  exact weight_identity i k j l _

/-- Total mass of a margin matrix. -/
theorem total_rowSum (M : Raw r c) : (∑ i, ∑ j, M i j) = ∑ i, rowSum M i := rfl

/-- `T'(γ) = (Σγ)² - Σγᵢ²`. -/
def tPrime {m : ℕ} (v : Fin m → ℕ) : ℤ := ((∑ i, v i : ℕ) : ℤ) ^ 2 - sqSum v

/-- The crossing bound `4·crossing M ≤ T'(β) + T'(α)` together with its exact defect. -/
theorem four_crossing_add_defect {β : Fin r → ℕ} {α : Fin c → ℕ} (M : Mat β α) :
    4 * (crossing M.val : ℤ) + defect M.val = tPrime β + tPrime α := by
  have hid := crossing_identity M.val
  have hr : (∑ i, ∑ j, M.val i j) = ∑ i, β i := by
    rw [total_rowSum, M.property.1]
  have hc : (∑ i, ∑ j, M.val i j) = ∑ j, α j := by
    rw [Finset.sum_comm]; exact congrArg (fun f => ∑ j, f j) M.property.2
  rw [M.property.1, M.property.2] at hid
  unfold tPrime
  rw [← hid, ← hr, ← hc]
  ring

theorem four_crossing_le {β : Fin r → ℕ} {α : Fin c → ℕ} (M : Mat β α) :
    4 * (crossing M.val : ℤ) ≤ tPrime β + tPrime α := by
  rw [← four_crossing_add_defect M]
  have : (0 : ℤ) ≤ defect M.val := Nat.cast_nonneg _
  linarith

theorem four_crossing_eq_iff {β : Fin r → ℕ} {α : Fin c → ℕ} (M : Mat β α) :
    4 * (crossing M.val : ℤ) = tPrime β + tPrime α ↔ defect M.val = 0 := by
  rw [← four_crossing_add_defect M]
  constructor
  · intro h; exact_mod_cast (by linarith : (defect M.val : ℤ) = 0)
  · intro h; rw [h]; simp

/-! ## The equality case -/

theorem defect_eq_zero_iff (M : Raw r c) :
    defect M = 0 ↔ ∀ i j k l, M i j * M k l * cellWeight i k j l = 0 := by
  unfold defect
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]

/-- The antidiagonal matrix with entries `β` (row `i` meets column `r-1-i`). -/
def antidiag (β : Fin r → ℕ) : Raw r c := fun i j => if j.val + i.val + 1 = r then β i else 0

theorem eq_antidiag_of_defect_eq_zero {β : Fin r → ℕ} {α : Fin c → ℕ} (M : Mat β α)
    (hβ : ∀ i, 0 < β i) (hα : ∀ j, 0 < α j) (hd : defect M.val = 0) :
    r = c ∧ M.val = antidiag β ∧ ∀ (j : Fin c) (i : Fin r), j.val + i.val + 1 = r → α j = β i := by
  have hz := (defect_eq_zero_iff M.val).mp hd
  -- row supports are singletons
  have hrow : ∀ i j l, 0 < M.val i j → 0 < M.val i l → j = l := by
    intro i j l h1 h2
    rcases eq_or_ne j l with h | hne
    · exact h
    exfalso
    have := hz i j i l
    have hw : 0 < cellWeight i i j l := by simp [cellWeight, hne]
    have := Nat.mul_pos (Nat.mul_pos h1 h2) hw
    omega
  have hcol : ∀ i k j, 0 < M.val i j → 0 < M.val k j → i = k := by
    intro i k j h1 h2
    rcases eq_or_ne i k with h | hne
    · exact h
    exfalso
    have := hz i j k j
    have hw : 0 < cellWeight i k j j := by simp [cellWeight, hne]
    have := Nat.mul_pos (Nat.mul_pos h1 h2) hw
    omega
  have hnest : ∀ i k j l, i < k → j < l → 0 < M.val i j → 0 < M.val k l → False := by
    intro i k j l hik hjl h1 h2
    have := hz i j k l
    have hw : 0 < cellWeight i k j l := by simp [cellWeight, hik, hjl]
    have := Nat.mul_pos (Nat.mul_pos h1 h2) hw
    omega
  -- each row has a nonzero entry
  have hex : ∀ i, ∃ j, 0 < M.val i j := by
    intro i
    by_contra h
    push_neg at h
    have h0 : rowSum M.val i = 0 := Finset.sum_eq_zero (fun j _ => Nat.le_zero.mp (h j))
    rw [M.property.1] at h0
    exact absurd h0 (Nat.pos_iff_ne_zero.mp (hβ i))
  have hexc : ∀ j, ∃ i, 0 < M.val i j := by
    intro j
    by_contra h
    push_neg at h
    have h0 : colSum M.val j = 0 := Finset.sum_eq_zero (fun i _ => Nat.le_zero.mp (h i))
    rw [M.property.2] at h0
    exact absurd h0 (Nat.pos_iff_ne_zero.mp (hα j))
  choose f hf using hex
  have finj : Function.Injective f := fun i k he => hcol i k (f i) (hf i) (he ▸ hf k)
  have fsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := hexc j
    exact ⟨i, hrow i (f i) j (hf i) hi⟩
  have hanti : ∀ i k, i < k → f k < f i := by
    intro i k hik
    rcases lt_trichotomy (f i) (f k) with h | h | h
    · exact (hnest i k (f i) (f k) hik h (hf i) (hf k)).elim
    · exact absurd (finj h) (ne_of_lt hik)
    · exact h
  have hrc : r = c := by
    simpa using Fintype.card_congr (Equiv.ofBijective f ⟨finj, fsurj⟩)
  subst hrc
  -- f is the reversal
  have hfrev : ∀ i, (f i).val + i.val + 1 = r := by
    have hmono : StrictMono (fun i => Fin.rev (f i)) := by
      intro i k hik
      exact Fin.rev_lt_rev.mpr (hanti i k hik)
    let e : Fin r ≃o Fin r := StrictMono.orderIsoOfSurjective _ hmono
      (fun j => by obtain ⟨i, hi⟩ := fsurj (Fin.rev j); exact ⟨i, by simp [hi]⟩)
    have he : e = OrderIso.refl (Fin r) := Subsingleton.elim _ _
    intro i
    have h1 := congrArg (fun g : Fin r ≃o Fin r => ((g i : Fin r) : ℕ)) he
    simp only [e, StrictMono.coe_orderIsoOfSurjective, OrderIso.refl_apply, Fin.val_rev] at h1
    have := (f i).isLt
    omega
  have hentry : ∀ i j, M.val i j = if j = f i then β i else 0 := by
    intro i j
    split_ifs with hj
    · subst hj
      have hs : rowSum M.val i = M.val i (f i) := by
        unfold rowSum
        rw [Finset.sum_eq_single (f i)]
        · intro l _ hl
          by_contra hne
          exact hl (hrow i l (f i) (Nat.pos_of_ne_zero hne) (hf i))
        · simp
      rw [← hs, M.property.1]
    · by_contra hne
      exact hj (hrow i j (f i) (Nat.pos_of_ne_zero hne) (hf i))
  refine ⟨rfl, ?_, ?_⟩
  · funext i j
    rw [hentry, antidiag]
    congr 1
    apply propext
    constructor
    · rintro rfl; exact hfrev i
    · intro h; apply Fin.ext; have := hfrev i; omega
  · intro j i hji
    have hj : j = f i := by apply Fin.ext; have := hfrev i; omega
    have hs : colSum M.val j = M.val i j := by
      unfold colSum
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        by_contra hne
        exact hk (hcol k i j (Nat.pos_of_ne_zero hne) (hj ▸ hf i))
      · simp
    rw [← M.property.2]
    change colSum M.val j = β i
    rw [hs, hentry, if_pos hj]

theorem defect_antidiag (β : Fin r → ℕ) : defect (antidiag (c := r) β) = 0 := by
  apply (defect_eq_zero_iff _).mpr
  intro i j k l
  unfold antidiag cellWeight
  by_cases h1 : j.val + i.val + 1 = r
  · by_cases h2 : l.val + k.val + 1 = r
    · rw [if_pos h1, if_pos h2]
      have e1 : i = k ↔ j = l := by
        constructor
        · intro h; subst h; apply Fin.ext; omega
        · intro h; subst h; apply Fin.ext; omega
      have e2 : i < k ↔ l < j := by
        rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val]; omega
      have e3 : k < i ↔ j < l := by
        rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val]; omega
      have w1 : ¬ (i = k ∧ j ≠ l) := fun h => h.2 (e1.mp h.1)
      have w2 : ¬ (j = l ∧ i ≠ k) := fun h => h.2 (e1.mpr h.1)
      have w3 : ¬ (i < k ∧ j < l) := fun h => absurd (e2.mp h.1) (not_lt.mpr (le_of_lt h.2))
      have w4 : ¬ (k < i ∧ l < j) := fun h => absurd (e3.mp h.1) (not_lt.mpr (le_of_lt h.2))
      rw [if_neg w1, if_neg w2, if_neg w3, if_neg w4]
      simp
    · rw [if_neg h2]; simp
  · rw [if_neg h1]; simp

/-- The antidiagonal matrix lies in `Mat β α` when `αⱼ = β_{r-1-j}`. -/
def antidiagMat (β : Fin r → ℕ) (α : Fin r → ℕ)
    (hα : ∀ (j i : Fin r), j.val + i.val + 1 = r → α j = β i) : Mat β α :=
  ⟨antidiag β, by
    constructor
    · funext i
      unfold rowSum antidiag
      rw [Finset.sum_eq_single (Fin.rev i)]
      · rw [if_pos (by simp only [Fin.val_rev]; omega)]
      · intro j _ hj
        rw [if_neg]
        intro h; apply hj; apply Fin.ext; simp only [Fin.val_rev]; omega
      · simp
    · funext j
      unfold colSum antidiag
      rw [Finset.sum_eq_single (Fin.rev j)]
      · rw [if_pos (by simp only [Fin.val_rev]; omega)]
        exact (hα j (Fin.rev j) (by simp only [Fin.val_rev]; omega)).symm
      · intro i _ hi
        rw [if_neg]
        intro h; apply hi; apply Fin.ext; simp only [Fin.val_rev]; omega
      · simp⟩

end OddMath.Frontier.EKGeneralQ

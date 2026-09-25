import Mathlib

/-! # Counting partitions in a box
Counting identities for partitions in a box, used for the graded rank comparisons of
EKL arXiv:1111.1320v1, §4.3–4.4 (Theorems 4.15–4.16).

* `pcount k n` is the number of partitions of `n` with at most `k` parts;
  its generating function is `∏_{i=1}^k (1 - q^i)⁻¹`.
* `box a b` is `P(a,b)`, the partitions with at most `a` parts, each at most `b`; its weight
  generating function is the Gaussian binomial `[a+b choose a]_q`, and
  `∏_{i ≤ a} (1 - q^i)⁻¹ ∏_{i ≤ b} (1 - q^i)⁻¹ = [a+b choose a]_q ∏_{i ≤ a+b} (1 - q^i)⁻¹`
  (`sum_pcount_mul`).
* `Sq a` is the staircase `S_q(a)` of EKL (4.37); its weight generating function is the
  `q`-factorial `[a]_q!`, and `(1 - q)^{-a} = [a]_q! ∏_{i ≤ a} (1 - q^i)⁻¹` (`monomial_count`).

The generating function identities are proved in `ℤ⟦X⟧` from the `q`-Pascal recursion
(removing the first row of a box partition) and the recursion removing a full first column.
-/
namespace OddMath.Frontier.BoxPartitionCount
open Finset PowerSeries

/-! ### Definitions -/

/-- Partitions of `n` with at most `k` parts, as antitone `k`-tuples summing to `n`. -/
def partitions (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.Nat.antidiagonalTuple k n).filter Antitone

/-- The number of partitions of `n` with at most `k` parts. -/
def pcount (k n : ℕ) : ℕ := (partitions k n).card

/-- `P(a,b)`: antitone `a`-tuples with entries at most `b`. -/
def box (a b : ℕ) : Finset (Fin a → ℕ) :=
  (Fintype.piFinset fun _ => range (b + 1)).filter Antitone

/-- The multiset of weights `|α|` of `α ∈ P(a,b)`. -/
def boxWeights (a b : ℕ) : Multiset ℕ := (box a b).val.map fun α => ∑ i, α i

/-- `S_q(a)` of EKL (4.37), 0-based: tuples `ℓ : Fin (a - 1) → ℕ` with `ℓ ν ≤ ν + 1`. -/
def Sq (a : ℕ) : Finset (Fin (a - 1) → ℕ) :=
  Fintype.piFinset fun ν => range (ν.val + 2)

theorem mem_partitions {k n : ℕ} {l : Fin k → ℕ} :
    l ∈ partitions k n ↔ Antitone l ∧ ∑ i, l i = n := by
  simp [partitions, Finset.Nat.mem_antidiagonalTuple, and_comm]

theorem mem_box {a b : ℕ} {α : Fin a → ℕ} : α ∈ box a b ↔ Antitone α ∧ ∀ i, α i ≤ b := by
  simp [box, Nat.lt_succ_iff, and_comm]

theorem mem_Sq {a : ℕ} {l : Fin (a - 1) → ℕ} : l ∈ Sq a ↔ ∀ ν, l ν ≤ ν.val + 1 := by
  simp [Sq, Nat.lt_succ_iff]

/-! ### Recursions -/

theorem pcount_zero (n : ℕ) : pcount 0 n = if n = 0 then 1 else 0 := by
  cases n <;> simp [pcount, partitions]
  decide

/-- Removing a zero last part, or subtracting a full first column. -/
theorem pcount_succ (m n : ℕ) :
    pcount (m + 1) n = pcount m n + if m + 1 ≤ n then pcount (m + 1) (n - (m + 1)) else 0 := by
  have hpos : ∀ l ∈ (partitions (m + 1) n).filter (fun l => ¬ l (Fin.last m) = 0), ∀ i, 1 ≤ l i :=
    fun l hl i => by
      simp only [mem_filter, mem_partitions] at hl
      exact (Nat.one_le_iff_ne_zero.2 hl.2).trans (hl.1.1 (Fin.le_last i))
  have hsum : ∀ l : Fin (m + 1) → ℕ, ∑ i, (l i + 1) = ∑ i, l i + (m + 1) := fun l => by
    simp [sum_add_distrib]
  rw [pcount, ← filter_card_add_filter_neg_card_eq_card (fun l => l (Fin.last m) = 0)]
  congr 1
  · refine card_nbij' Fin.init (fun μ => Fin.snoc μ 0) ?_ ?_ ?_ ?_
    · intro l hl
      simp only [mem_filter, mem_partitions] at hl ⊢
      refine ⟨hl.1.1.comp_monotone Fin.strictMono_castSucc.monotone, ?_⟩
      rw [← hl.1.2, Fin.sum_univ_castSucc, hl.2, add_zero]
      rfl
    · intro μ hμ
      simp only [mem_filter, mem_partitions, Fin.snoc_last,
        and_true] at hμ ⊢
      refine ⟨fun i j hij => ?_, ?_⟩
      · cases i using Fin.lastCases <;> cases j using Fin.lastCases
        · exact le_rfl
        · exact absurd hij (by simp [Fin.le_def])
        · simp
        · simpa using hμ.1 (Fin.castSucc_le_castSucc_iff.1 hij)
      · simpa [Fin.sum_univ_castSucc] using hμ.2
    · intro l hl
      simp only [mem_filter] at hl
      conv_rhs => rw [← Fin.snoc_init_self l, hl.2]
    · intro μ _
      exact Fin.init_snoc _ _
  · split_ifs with h
    · refine card_nbij' (fun l i => l i - 1) (fun ν i => ν i + 1) ?_ ?_ ?_ ?_
      · intro l hl
        have h1 := hpos l hl
        simp only [mem_filter, mem_partitions] at hl ⊢
        refine ⟨fun i j hij => Nat.sub_le_sub_right (hl.1.1 hij) 1, ?_⟩
        have := hsum fun i => l i - 1
        simp only [Nat.sub_add_cancel (h1 _)] at this
        omega
      · intro ν hν
        simp only [mem_filter, mem_partitions] at hν ⊢
        refine ⟨⟨fun i j hij => Nat.add_le_add_right (hν.1 hij) 1, ?_⟩, by simp⟩
        rw [hsum, hν.2]
        omega
      · intro l hl
        funext i
        exact Nat.sub_add_cancel (hpos l hl i)
      · intro ν _
        funext i
        simp
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro l hl hl0
      have h1 := hpos l (mem_filter.2 ⟨hl, hl0⟩)
      have := hsum fun i => l i - 1
      simp only [Nat.sub_add_cancel (h1 _), (mem_partitions.1 hl).2] at this
      omega

theorem card_antidiagonalTuple_succ (k n : ℕ) :
    (Finset.Nat.antidiagonalTuple (k + 1) n).card =
      ∑ p ∈ antidiagonal n, (Finset.Nat.antidiagonalTuple k p.2).card := by
  show (List.Nat.antidiagonalTuple (k + 1) n).length =
    ((List.Nat.antidiagonal n).map fun p => (List.Nat.antidiagonalTuple k p.2).length).sum
  simp [List.Nat.antidiagonalTuple, List.length_flatMap]

theorem box_zero_right (a : ℕ) : box a 0 = {0} := by
  ext α
  simp only [mem_box, nonpos_iff_eq_zero, mem_singleton]
  exact ⟨fun h => funext h.2, fun h => h ▸ ⟨antitone_const, fun _ => rfl⟩⟩

theorem box_zero_left (b : ℕ) : box 0 b = {0} := by
  ext α
  simp only [mem_box, mem_singleton]
  exact ⟨fun _ => funext (Fin.elim0 ·), fun _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩

/-- The `q`-Pascal recursion for `P(a+1,b+1)`, splitting off a full first row. -/
theorem sum_box_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ α ∈ box (a + 1) (b + 1), f (∑ i, α i) =
      ∑ α ∈ box (a + 1) b, f (∑ i, α i) + ∑ β ∈ box a (b + 1), f (b + 1 + ∑ i, β i) := by
  rw [← sum_filter_add_sum_filter_not (box (a + 1) (b + 1)) (fun α => α 0 ≤ b)]
  congr 1
  · refine sum_congr (ext fun α => ?_) fun _ _ => rfl
    simp only [mem_filter, mem_box]
    constructor
    · rintro ⟨⟨h, -⟩, h0⟩
      exact ⟨h, fun i => (h (Fin.zero_le i)).trans h0⟩
    · rintro ⟨h, hb⟩
      exact ⟨⟨h, fun i => (hb i).trans b.le_succ⟩, hb 0⟩
  · refine sum_nbij' Fin.tail (fun β => Fin.cons (b + 1) β) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [mem_filter, mem_box, not_le] at hα ⊢
      exact ⟨hα.1.1.comp_monotone (Fin.strictMono_succ.monotone), fun i => hα.1.2 _⟩
    · intro β hβ
      simp only [mem_filter, mem_box, not_le, Fin.cons_zero, lt_add_iff_pos_right,
        zero_lt_one, and_true] at hβ ⊢
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · cases i using Fin.cases <;> cases j using Fin.cases
        · exact le_rfl
        · simpa using hβ.2 _
        · exact absurd hij (by simp [Fin.le_def])
        · simpa using hβ.1 (Fin.succ_le_succ_iff.1 hij)
      · cases i using Fin.cases
        · simp
        · simpa using hβ.2 _
    · intro α hα
      simp only [mem_filter, mem_box, not_le] at hα
      have h0 : α 0 = b + 1 := le_antisymm (hα.1.2 0) hα.2
      conv_rhs => rw [← Fin.cons_self_tail α, h0]
    · intro β _
      exact Fin.tail_cons _ _
    · intro α hα
      simp only [mem_filter, mem_box, not_le] at hα
      have h0 : α 0 = b + 1 := le_antisymm (hα.1.2 0) hα.2
      rw [Fin.sum_univ_succ, h0]
      rfl

theorem card_box_succ (a b : ℕ) :
    (box (a + 1) (b + 1)).card = (box (a + 1) b).card + (box a (b + 1)).card := by
  simpa using sum_box_succ (fun _ => (1 : ℕ)) a b

/-- `#P(a,b) = C(a+b, a)`. -/
theorem card_box (a b : ℕ) : (box a b).card = (a + b).choose a := by
  induction a generalizing b with
  | zero => simp [box_zero_left]
  | succ a iha =>
    induction b with
    | zero => simp [box_zero_right]
    | succ b ihb =>
      rw [card_box_succ, ihb, iha, show a + 1 + (b + 1) = a + b + 1 + 1 by omega,
        Nat.choose_succ_succ', show a + 1 + b = a + b + 1 by omega,
        show a + (b + 1) = a + b + 1 by omega, add_comm]

theorem card_boxWeights (a b : ℕ) : Multiset.card (boxWeights a b) = (a + b).choose a := by
  simp [boxWeights, ← card_box]

/-- `#S_q(a) = a!`. -/
theorem card_Sq (a : ℕ) : (Sq a).card = a.factorial := by
  have h : ∀ c, ∏ i ∈ range c, (i + 2) = (c + 1).factorial := fun c => by
    induction c with
    | zero => rfl
    | succ c ih => rw [prod_range_succ, ih, Nat.factorial_succ (c + 1), mul_comm]
  rw [Sq, Fintype.card_piFinset]
  simp only [card_range]
  rw [Fin.prod_univ_eq_prod_range (fun i => i + 2)]
  cases a with
  | zero => rfl
  | succ c => exact h c

/-! ### Generating functions -/

/-- `(q;q)_n = ∏_{i=1}^n (1 - q^i)`. -/
noncomputable def qPoch (n : ℕ) : ℤ⟦X⟧ := ∏ i ∈ range n, (1 - X ^ (i + 1))

/-- The generating function `∑_n pcount k n q^n`. -/
noncomputable def pgf (k : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n => (pcount k n : ℤ)

/-- The Gaussian binomial `[a+b choose a]_q = ∑_{α ∈ P(a,b)} q^{|α|}`. -/
noncomputable def gauss (a b : ℕ) : ℤ⟦X⟧ := ∑ α ∈ box a b, X ^ ∑ i, α i

/-- The `q`-factorial `[a]_q! = ∑_{ℓ ∈ S_q(a)} q^{|ℓ|}`. -/
noncomputable def qfact (a : ℕ) : ℤ⟦X⟧ := ∑ l ∈ Sq a, X ^ ∑ ν, l ν

/-- The generating function of monomials in `a` variables, `∑_d #{γ | |γ| = d} q^d`. -/
noncomputable def mgf (a : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d => ((Finset.Nat.antidiagonalTuple a d).card : ℤ)

theorem qPoch_succ (n : ℕ) : qPoch (n + 1) = qPoch n * (1 - X ^ (n + 1)) := prod_range_succ _ _

theorem pgf_succ (m : ℕ) : pgf (m + 1) = pgf m + X ^ (m + 1) * pgf (m + 1) := by
  ext n
  rw [map_add, coeff_X_pow_mul']
  simp only [pgf, coeff_mk]
  rw [pcount_succ m n]
  split_ifs <;> simp

theorem pgf_mul_qPoch (k : ℕ) : pgf k * qPoch k = 1 := by
  induction k with
  | zero =>
    ext n
    simp [pgf, qPoch, pcount_zero, coeff_one]
  | succ m ih =>
    rw [qPoch_succ]
    linear_combination qPoch m * pgf_succ m + ih

theorem gauss_succ (a b : ℕ) :
    gauss (a + 1) (b + 1) = gauss (a + 1) b + X ^ (b + 1) * gauss a (b + 1) := by
  simp [gauss, sum_box_succ (fun w => (X : ℤ⟦X⟧) ^ w), pow_add, mul_sum]

theorem gauss_mul_qPoch (a b : ℕ) : gauss a b * qPoch a * qPoch b = qPoch (a + b) := by
  induction a generalizing b with
  | zero => simp [gauss, box_zero_left, qPoch]
  | succ a iha =>
    induction b with
    | zero => simp [gauss, box_zero_right, qPoch]
    | succ b ihb =>
      have h1 := ihb
      have h2 := iha (b + 1)
      rw [show a + 1 + b = a + b + 1 by omega] at h1
      rw [show a + (b + 1) = a + b + 1 by omega] at h2
      rw [show a + 1 + (b + 1) = a + b + 1 + 1 by omega, gauss_succ]
      simp only [qPoch_succ] at h1 h2 ⊢
      linear_combination (1 - X ^ (b + 1)) * h1 + X ^ (b + 1) * (1 - X ^ (a + 1)) * h2

/-- `∏_{i≤a} (1-q^i)⁻¹ ∏_{i≤b} (1-q^i)⁻¹ = [a+b choose a]_q ∏_{i≤a+b} (1-q^i)⁻¹`. -/
theorem pgf_mul_pgf (a b : ℕ) : pgf a * pgf b = gauss a b * pgf (a + b) := by
  linear_combination (-(pgf a * pgf b)) * pgf_mul_qPoch (a + b) -
    pgf a * pgf b * pgf (a + b) * gauss_mul_qPoch a b +
    gauss a b * pgf (a + b) * (pgf b * qPoch b) * pgf_mul_qPoch a +
    gauss a b * pgf (a + b) * pgf_mul_qPoch b

theorem qfact_mul (a : ℕ) : qfact a * (1 - X) ^ a = qPoch a := by
  have h : qfact a = ∏ i ∈ range (a - 1), ∑ x ∈ range (i + 2), (X : ℤ⟦X⟧) ^ x := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∑ x ∈ range (i + 2), (X : ℤ⟦X⟧) ^ x),
      prod_univ_sum]
    simp [qfact, Sq, prod_pow_eq_pow_sum]
  rw [h]
  cases a with
  | zero => simp [qPoch]
  | succ c =>
    have hc : (1 - X : ℤ⟦X⟧) ^ c = ∏ _i ∈ range c, (1 - X) := by simp
    rw [Nat.add_sub_cancel, qPoch, prod_range_succ', pow_succ, hc, ← mul_assoc,
      ← prod_mul_distrib]
    congr 1
    · exact prod_congr rfl fun i _ => by rw [geom_sum_mul_neg]
    · simp

theorem mgf_eq (a : ℕ) : mgf a = PowerSeries.mk 1 ^ a := by
  induction a with
  | zero =>
    ext d
    cases d <;> simp [mgf]
  | succ a ih =>
    ext d
    rw [pow_succ', ← ih, coeff_mul]
    simp [mgf, card_antidiagonalTuple_succ]

theorem mgf_mul (a : ℕ) : mgf a * (1 - X) ^ a = 1 := by
  rw [mgf_eq, ← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]

/-- `(1-q)^{-a} = [a]_q! ∏_{i≤a} (1-q^i)⁻¹`. -/
theorem mgf_eq_qfact_mul (a : ℕ) : mgf a = qfact a * pgf a := by
  linear_combination (-mgf a) * pgf_mul_qPoch a - mgf a * pgf a * qfact_mul a +
    qfact a * pgf a * mgf_mul a

theorem coeff_sum_X_pow_mul {ι : Type*} (s : Finset ι) (w : ι → ℕ) (f : ℕ → ℤ) (j : ℕ) :
    coeff ℤ j ((∑ x ∈ s, X ^ w x) * PowerSeries.mk f) =
      ∑ x ∈ s.filter (fun x => w x ≤ j), f (j - w x) := by
  rw [sum_mul, map_sum, sum_filter]
  exact sum_congr rfl fun x _ => by rw [coeff_X_pow_mul', coeff_mk]

/-! ### Counting identities -/

/-- Coefficientwise form of `pgf_mul_pgf`. -/
theorem sum_pcount_mul (a b j : ℕ) :
    ∑ i ∈ range (j + 1), pcount a i * pcount b (j - i) =
      ∑ α ∈ (box a b).filter (fun α => ∑ i, α i ≤ j), pcount (a + b) (j - ∑ i, α i) := by
  apply Nat.cast_injective (R := ℤ)
  have h := congrArg (coeff ℤ j) (pgf_mul_pgf a b)
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, gauss] at h
  simp only [pgf] at h
  rw [coeff_sum_X_pow_mul] at h
  push_cast
  simpa [pgf] using h

/-- `sum_pcount_mul` with the right side indexed by the weights `boxWeights a b`. -/
theorem sum_pcount_mul_boxWeights (a b j : ℕ) :
    ∑ i ∈ range (j + 1), pcount a i * pcount b (j - i) =
      (((boxWeights a b).filter (· ≤ j)).map fun w => pcount (a + b) (j - w)).sum := by
  rw [sum_pcount_mul, boxWeights, Multiset.filter_map, Multiset.map_map]
  rfl

/-- Stars and bars: `#{γ : Fin a → ℕ | |γ| = d} = C(d+a-1, a-1)` for `a ≥ 1`. -/
theorem card_monomials {a : ℕ} (ha : 0 < a) (d : ℕ) :
    (Finset.Nat.antidiagonalTuple a d).card = (d + a - 1).choose (a - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  have h := congrArg (coeff ℤ d) (mgf_eq (c + 1))
  rw [mk_one_pow_eq_mk_choose_add] at h
  simp only [mgf, coeff_mk, Nat.cast_inj] at h
  rw [h, Nat.add_sub_cancel, show d + (c + 1) - 1 = c + d by omega]

/-- Coefficientwise form of `mgf_eq_qfact_mul`: monomials of degree `d` in `a` variables
counted through `S_q(a)` and partitions with at most `a` parts. -/
theorem monomial_count (a d : ℕ) :
    (Finset.Nat.antidiagonalTuple a d).card =
      ∑ l ∈ (Sq a).filter (fun l => ∑ ν, l ν ≤ d), pcount a (d - ∑ ν, l ν) := by
  apply Nat.cast_injective (R := ℤ)
  have h := congrArg (coeff ℤ d) (mgf_eq_qfact_mul a)
  rw [qfact, pgf, coeff_sum_X_pow_mul] at h
  push_cast
  simpa [mgf] using h

end OddMath.Frontier.BoxPartitionCount

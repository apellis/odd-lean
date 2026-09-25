import OddMath.Frontier.OddSchurPieri
import OddMath.Frontier.ElementaryBasis
import OddMath.Frontier.ElementaryRelations

/-! EKL arXiv:1111.1320v1, §2.3, Remark 2.28, display (2.76), p.20.

For α = (2,2) the remark prints
`h₂₂ - h₃₁ = (ε₂₂ - 2ε₂₁₁ + ε₁₁₁₁) - (ε₃₁ - ε₁₁₁)` and `s₂₂ = ε₂₂ + ε₃₁ - 2ε₄`,
with `ε_α = ε_{α₁}ε_{α₂}⋯`, `h_α = h_{α₁}h_{α₂}⋯` and `s_α` the odd Schur
polynomial of Definition 2.24. The two determinant lines are correct, the three
expansions are not. Proved here:
* `h₂₂ = ε₂₂ + 2ε₂₁₁ + ε₁₁₁₁` and `h₃₁ = ε₃₁ + ε₁₁₁₁` in every rank;
* `s₂₂ = -ε₂₂ + ε₃₁ + 2ε₄` in every rank `a ≥ 4`;
* the printed `h₂₂`, `h₃₁` and `s₂₂` expansions fail (the last also up to a global sign).
Rank `a ≥ 4` is `SkewPolynomial (n+4)`; the Schur polynomials there are `schur (n+2)`. -/
namespace OddMath.Frontier.EKLSectionTwo
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open OddSymmetrizer OddSchurPieri FiniteCompleteElementary ElementaryGeneration
open scoped BigOperators
noncomputable section

/-! ### Complete polynomials in low degree -/

section Complete
variable (N : ℕ)

local notation "e" => elementaryPoly N
local notation "h" => completePoly N

/-- (2.31) with `m = 1`. -/
theorem complete_one : h 1 = e 1 := by
  have hh := elementary_complete_inverse N 1 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hh
  norm_num [Nat.choose] at hh
  rw [← sub_eq_zero]; convert hh using 1; abel

/-- (2.31) with `m = 2`. -/
theorem complete_two : h 2 = e 1 * e 1 + e 2 := by
  have hh := elementary_complete_inverse N 2 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hh
  norm_num [Nat.choose] at hh
  rw [complete_one] at hh
  rw [← sub_eq_zero]; convert hh using 1; abel

/-- (2.22), third relation with `m = 1`. -/
theorem anticommutator_one_two : e 1 * e 2 + e 2 * e 1 = (2 : ℤ) • e 3 := by
  simpa using ElementaryRelations.elementary_one_even N 1

/-- (2.31) with `m = 3`, reduced by (2.22). -/
theorem complete_three : h 3 = e 1 * e 1 * e 1 + e 3 := by
  have hh := elementary_complete_inverse N 3 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hh
  norm_num [Nat.choose] at hh
  rw [complete_one, complete_two] at hh
  have ha := anticommutator_one_two N
  have h3 : h 3 = e 1 * (e 1 * e 1 + e 2) + e 2 * e 1 - e 3 := by
    rw [← sub_eq_zero]; convert hh using 1; abel
  rw [h3, mul_add, ← mul_assoc, add_assoc, ha, two_smul]
  abel

theorem one_three_comm : e 1 * e 3 = e 3 * e 1 :=
  ElementaryRelations.elementary_even N 1 3 (by decide)

/-- `ε₁ε₁ε₂ = ε₂ε₁ε₁`, from (2.22). -/
theorem one_one_two : e 1 * e 1 * e 2 = e 2 * e 1 * e 1 := by
  have ha := anticommutator_one_two N
  have h12 : e 1 * e 2 = (2 : ℤ) • e 3 - e 2 * e 1 := eq_sub_of_add_eq ha
  rw [mul_assoc, h12, mul_sub, mul_smul_comm, ← mul_assoc (e 1) (e 2), h12, sub_mul,
    smul_mul_assoc, one_three_comm]
  abel

/-- Corrected (2.76): `h₂₂ = ε₂₂ + 2ε₂₁₁ + ε₁₁₁₁`, in every rank. -/
theorem complete_two_two :
    h 2 * h 2 = e 2 * e 2 + (2 : ℤ) • (e 2 * e 1 * e 1) + e 1 * e 1 * e 1 * e 1 := by
  rw [complete_two, mul_add, add_mul, add_mul]
  simp only [← mul_assoc]
  rw [one_one_two, two_smul]
  abel

/-- Corrected (2.76): `h₃₁ = ε₃₁ + ε₁₁₁₁`, in every rank. -/
theorem complete_three_one : h 3 * h 1 = e 3 * e 1 + e 1 * e 1 * e 1 * e 1 := by
  rw [complete_three, complete_one, add_mul]
  abel

/-- The determinant line of (2.76) in corrected form: `h₂₂ - h₃₁ = ε₂₂ + 2ε₂₁₁ - ε₃₁`. -/
theorem complete_determinant :
    h 2 * h 2 - h 3 * h 1 = e 2 * e 2 + (2 : ℤ) • (e 2 * e 1 * e 1) - e 3 * e 1 := by
  rw [complete_two_two, complete_three_one]; abel

end Complete

/-! ### Leading coefficients -/

/-- Leading term of an ordered product `ε_{k₁}⋯ε_{k_r}` of elementary polynomials. -/
theorem word_leading (N : ℕ) (w : List ℕ) (hw : ∀ k ∈ w, k ≤ N) :
    ∃ c : ℤ, c * c = 1 ∧
      Leading (elementaryWord N w) (columnExponent N w) c := by
  induction w with
  | nil =>
    refine ⟨1, by norm_num, ?_⟩
    simp only [elementaryWord, columnExponent, List.map_nil, List.prod_nil, List.sum_nil]
    exact ⟨bounded_single _ _, Finsupp.single_eq_same⟩
  | cons k w ih =>
    obtain ⟨c, hc, hl⟩ := ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
    obtain ⟨d, hd, hk⟩ := elementary_leading N k (hw k List.mem_cons_self)
    refine ⟨d * c * OddMath.skewSign (prefixExp N k) (columnExponent N w), ?_, ?_⟩
    · have hs : OddMath.skewSign (prefixExp N k) (columnExponent N w) *
          OddMath.skewSign (prefixExp N k) (columnExponent N w) = 1 := by
        unfold OddMath.skewSign; rw [← mul_pow]; norm_num
      calc _ = (d * d) * (c * c) * (OddMath.skewSign (prefixExp N k) (columnExponent N w) *
            OddMath.skewSign (prefixExp N k) (columnExponent N w)) := by ring
        _ = 1 := by rw [hd, hc, hs]; norm_num
    · have := leading_mul hk hl
      simpa [elementaryWord, columnExponent] using this

theorem word_coeff_unit (N : ℕ) (w : List ℕ) (hw : ∀ k ∈ w, k ≤ N) :
    elementaryWord N w (columnExponent N w) ≠ 0 := by
  obtain ⟨c, hc, hl⟩ := word_leading N w hw
  rw [hl.2]
  rintro rfl
  norm_num at hc

theorem word_coeff_above (N : ℕ) (w : List ℕ) (hw : ∀ k ∈ w, k ≤ N) (b : Fin N → ℕ)
    (hb : toLex (columnExponent N w) < toLex b) : elementaryWord N w b = 0 := by
  obtain ⟨c, _, hl⟩ := word_leading N w hw
  by_contra hne
  exact absurd (hl.1 b hne) (not_le.mpr hb)

theorem word_coeff_degree (N : ℕ) (w : List ℕ) (b : Fin N → ℕ)
    (hb : ∑ i, b i ≠ w.sum) : elementaryWord N w b = 0 :=
  ElementaryBasis.word_homogeneous N w b hb

theorem elementaryWord_two (N a b : ℕ) :
    elementaryWord N [a, b] = elementaryPoly N a * elementaryPoly N b := by
  simp [elementaryWord]

theorem elementaryWord_three (N a b c : ℕ) :
    elementaryWord N [a, b, c] = elementaryPoly N a * elementaryPoly N b * elementaryPoly N c := by
  simp [elementaryWord, mul_assoc]

theorem elementaryWord_four (N a b c d : ℕ) :
    elementaryWord N [a, b, c, d] =
      elementaryPoly N a * elementaryPoly N b * elementaryPoly N c * elementaryPoly N d := by
  simp [elementaryWord, mul_assoc]

theorem elementaryWord_one (N a : ℕ) : elementaryWord N [a] = elementaryPoly N a := by
  simp [elementaryWord]

/-! ### The printed h-expansions fail -/

/-- Refutation of the printed `h₂₂ = ε₂₂ - 2ε₂₁₁ + ε₁₁₁₁` of (2.76), in every rank `a ≥ 2`. -/
theorem printed_complete_two_two_false (n : ℕ) :
    completePoly (n+2) 2 * completePoly (n+2) 2 ≠
      elementaryPoly (n+2) 2 * elementaryPoly (n+2) 2 -
        (2 : ℤ) • (elementaryPoly (n+2) 2 * elementaryPoly (n+2) 1 * elementaryPoly (n+2) 1) +
        elementaryPoly (n+2) 1 * elementaryPoly (n+2) 1 * elementaryPoly (n+2) 1 *
          elementaryPoly (n+2) 1 := by
  intro hp
  rw [complete_two_two] at hp
  have h4 : (4 : ℤ) • (elementaryPoly (n+2) 2 * elementaryPoly (n+2) 1 *
      elementaryPoly (n+2) 1) = 0 := by
    have := sub_eq_zero.mpr hp
    rw [← this]; module
  have hc := congrArg (fun f : SkewPolynomial (n+2) => f (columnExponent (n+2) [2, 1, 1])) h4
  dsimp only at hc
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
    ← elementaryWord_three] at hc
  exact word_coeff_unit (n+2) [2, 1, 1] (by simp) (by linarith)

/-- Refutation of the printed `h₃₁ = ε₃₁ - ε₁₁₁` of (2.76), in every rank `a ≥ 1`. -/
theorem printed_complete_three_one_false (n : ℕ) :
    completePoly (n+1) 3 * completePoly (n+1) 1 ≠
      elementaryPoly (n+1) 3 * elementaryPoly (n+1) 1 -
        elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1 := by
  intro hp
  rw [complete_three_one] at hp
  have hc := congrArg (fun f : SkewPolynomial (n+1) => f (columnExponent (n+1) [1, 1, 1])) hp
  simp only [Finsupp.add_apply, Finsupp.sub_apply] at hc
  rw [← elementaryWord_two, ← elementaryWord_four, ← elementaryWord_three] at hc
  have hsum : ∑ i, columnExponent (n+1) [1, 1, 1] i = 3 := by
    have := ElementaryBasis.word_homogeneous (n+1) [1, 1, 1]
    have hne := word_coeff_unit (n+1) [1, 1, 1] (by simp)
    by_contra hh
    exact hne (this _ (by simpa using hh))
  have h4 := word_coeff_degree (n+1) [1, 1, 1, 1] (columnExponent (n+1) [1, 1, 1])
    (by rw [hsum]; simp)
  have h31 := word_coeff_degree (n+1) [3, 1] (columnExponent (n+1) [1, 1, 1])
    (by rw [hsum]; simp)
  rw [h4, h31] at hc
  exact word_coeff_unit (n+1) [1, 1, 1] (by simp) (by linarith)

/-- Refutation of the printed determinant line of (2.76),
`h₂₂ - h₃₁ = (ε₂₂ - 2ε₂₁₁ + ε₁₁₁₁) - (ε₃₁ - ε₁₁₁)`, in every rank `a ≥ 1`. -/
theorem printed_complete_determinant_false (n : ℕ) :
    completePoly (n+1) 2 * completePoly (n+1) 2 - completePoly (n+1) 3 * completePoly (n+1) 1 ≠
      (elementaryPoly (n+1) 2 * elementaryPoly (n+1) 2 -
        (2 : ℤ) • (elementaryPoly (n+1) 2 * elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1) +
        elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1 *
          elementaryPoly (n+1) 1) -
      (elementaryPoly (n+1) 3 * elementaryPoly (n+1) 1 -
        elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1 * elementaryPoly (n+1) 1) := by
  intro hp
  rw [complete_determinant, ← elementaryWord_four (n+1) 1 1 1 1,
    ← elementaryWord_three (n+1) 2 1 1, ← elementaryWord_three (n+1) 1 1 1,
    ← elementaryWord_two (n+1) 2 2, ← elementaryWord_two (n+1) 3 1] at hp
  have hc := congrArg (fun f : SkewPolynomial (n+1) => f (columnExponent (n+1) [1, 1, 1])) hp
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at hc
  have hsum : ∑ i, columnExponent (n+1) [1, 1, 1] i = 3 := by
    have := ElementaryBasis.word_homogeneous (n+1) [1, 1, 1]
    have hne := word_coeff_unit (n+1) [1, 1, 1] (by simp)
    by_contra hh
    exact hne (this _ (by simpa using hh))
  have z : ∀ w : List ℕ, w.sum = 4 → elementaryWord (n+1) w (columnExponent (n+1) [1, 1, 1]) = 0 :=
    fun w hw => word_coeff_degree (n+1) w _ (by rw [hsum, hw]; omega)
  rw [z [2, 2] rfl, z [2, 1, 1] rfl, z [1, 1, 1, 1] rfl, z [3, 1] rfl] at hc
  exact word_coeff_unit (n+1) [1, 1, 1] (by simp) (by linarith)

/-! ### The odd Schur polynomial `s₂₂` -/

/-- Boxes below row `i` in the column `(1^k)`. -/
theorem column_tail (n k : ℕ) (hk : k ≤ n+2) (i : Fin (n+2)) :
    ∑ j ∈ Finset.univ.filter (i < ·), (column n k).val j = k - (i.val + 1) := by
  classical
  change ∑ j ∈ Finset.univ.filter (i < ·), (if j.val < k then 1 else 0) = _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    mul_one, Finset.filter_filter]
  have hm : (Finset.univ.filter fun j : Fin (n+2) => i < j ∧ j.val < k).map Fin.valEmbedding =
      Finset.Ioo i.val (min k (n+2)) := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ioo]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, lt_min h2 j.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, lt_of_lt_of_le h2 (min_le_right _ _)⟩, ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩,
        rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm, Nat.card_Ioo]
  have := i.isLt
  omega

theorem lowerRows_column (n k : ℕ) (hk : k ≤ n+2) (I : Finset (Fin (n+2))) :
    lowerRows (column n k).val I = ∑ i ∈ I, (k - (i.val + 1)) :=
  Finset.sum_congr rfl fun i _ => column_tail n k hk i

/-- Reindexing a vertical-strip Pieri sum by an explicit finite set of row sets. -/
theorem strip_sum {n k : ℕ} {α : PartitionExponent n} (S : Finset (Finset (Fin (n+2))))
    (hS : ∀ I, (I.card = k ∧ Antitone (increment α.val I)) ↔ I ∈ S)
    (g : Finset (Fin (n+2)) → SkewPolynomial (n+2))
    (hg : ∀ I (h : Antitone (increment α.val I)), I ∈ S →
      (-1 : ℤ)^lowerRows α.val I • schur n ⟨increment α.val I, h⟩ = g I) :
    ∑ I : VerticalStrip n k α, (-1 : ℤ)^lowerRows α.val I.val • schur n (stripPartition I) =
      ∑ I ∈ S, g I := by
  rw [← Finset.sum_coe_sort S]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight hS) _ _
    (fun I => hg I.1 I.2.2 ((hS _).1 I.2))

section Schur
variable (n : ℕ)

/-- The partition `(2,2)`, padded by zeros. -/
def twoTwo : PartitionExponent n :=
  ⟨fun i => if i.val < 2 then 2 else 0, by intro i j hij; dsimp; split_ifs <;> omega⟩

/-- The partition `(2,1,1)`, padded by zeros. -/
def twoOneOne : PartitionExponent n :=
  ⟨fun i => if i.val = 0 then 2 else if i.val < 3 then 1 else 0, by
    intro i j hij; dsimp; split_ifs <;> omega⟩

/-- EKL Definition 2.24: `s₂₂ = S(x₁²x₂²)`. -/
abbrev s22 : SkewPolynomial (n+2) := schur n (twoTwo n)

/-- EKL Definition 2.24: `s₂₁₁ = S(x₁²x₂x₃)`. -/
abbrev s211 : SkewPolynomial (n+2) := schur n (twoOneOne n)

/-- Row index `m` of the alphabet `Fin (n+4)`. -/
def r (m : ℕ) (h : m < n+4) : Fin (n+4) := ⟨m, h⟩

@[simp] theorem r_val (m : ℕ) (h : m < n+4) : (r n m h).val = m := rfl

variable {n}

theorem below_mem {c : ℕ} {I : Finset (Fin (n+4))}
    (hA : Antitone (increment (column (n+2) c).val I)) (t : Fin (n+4)) (ht : t ∈ I)
    (hc : c < t.val) :
    r n (t.val - 1) (by omega) ∈ I := by
  classical
  have hle : r n (t.val - 1) (by omega) ≤ t := Fin.le_def.mpr (by simp)
  have := hA hle
  simp only [increment, column, ht, if_true, r_val] at this
  by_contra hne
  rw [if_neg hne] at this
  split_ifs at this <;> (try simp only [r_val] at *) <;> omega

theorem top_mem {c : ℕ} {I : Finset (Fin (n+4))}
    (hA : Antitone (increment (column (n+2) c).val I)) (t : Fin (n+4)) (ht : t ∈ I)
    (hc : t.val < c) : r n 0 (by omega) ∈ I := by
  classical
  have hle : r n 0 (by omega) ≤ t := Fin.le_def.mpr (by simp)
  have := hA hle
  simp only [increment, column, ht, if_true, r_val] at this
  by_contra hne
  rw [if_neg hne] at this
  split_ifs at this <;> (try simp only [r_val] at *) <;> omega

variable (n)

theorem strip_column_two (I : Finset (Fin (n+4))) :
    (I.card = 2 ∧ Antitone (increment (column (n+2) 2).val I)) ↔
      I ∈ ({{r n 0 (by omega), r n 1 (by omega)}, {r n 0 (by omega), r n 2 (by omega)},
        {r n 2 (by omega), r n 3 (by omega)}} : Finset (Finset (Fin (n+4)))) := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hA⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have key : ∀ x y : Fin (n+4), x < y →
        Antitone (increment (column (n+2) 2).val {x, y}) →
        x.val = 0 ∧ y.val = 1 ∨ x.val = 0 ∧ y.val = 2 ∨ x.val = 2 ∧ y.val = 3 := by
      intro x y hlt hA
      have hv : x.val < y.val := hlt
      have hy : y ∈ ({x, y} : Finset (Fin (n+4))) := by simp
      have hx : x ∈ ({x, y} : Finset (Fin (n+4))) := by simp
      by_cases hy3 : 3 ≤ y.val
      · have h1 := below_mem hA y hy (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val] at h1
        by_cases hx3 : 3 ≤ x.val
        · have h2 := below_mem hA x hx (by omega)
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val] at h2
          omega
        · omega
      · by_cases hx1 : x.val = 1
        · have h2 := top_mem hA x hx (by omega)
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val] at h2
          omega
        · omega
    have fin : ∀ x y : Fin (n+4), x.val = 0 ∧ y.val = 1 ∨ x.val = 0 ∧ y.val = 2 ∨
        x.val = 2 ∧ y.val = 3 →
        ({x, y} : Finset (Fin (n+4))) = {r n 0 (by omega), r n 1 (by omega)} ∨
        ({x, y} : Finset (Fin (n+4))) = {r n 0 (by omega), r n 2 (by omega)} ∨
        ({x, y} : Finset (Fin (n+4))) = {r n 2 (by omega), r n 3 (by omega)} := by
      intro x y h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [show x = r n 0 (by omega) from Fin.ext h1, show y = r n 1 (by omega) from Fin.ext h2]
      · right; left
        rw [show x = r n 0 (by omega) from Fin.ext h1, show y = r n 2 (by omega) from Fin.ext h2]
      · right; right
        rw [show x = r n 2 (by omega) from Fin.ext h1, show y = r n 3 (by omega) from Fin.ext h2]
    rcases lt_or_gt_of_ne hxy with h | h
    · exact fin x y (key x y h hA)
    · rw [Finset.pair_comm] at hA ⊢
      exact fin y x (key y x h hA)
  · rintro (rfl | rfl | rfl) <;>
    · refine ⟨Finset.card_pair (by simp [Fin.ext_iff]), fun i j hij => ?_⟩
      have hij' : i.val ≤ j.val := hij
      simp only [increment, column, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val]
      split_ifs <;> (try simp only [r_val] at *) <;> omega

theorem strip_column_three (I : Finset (Fin (n+4))) :
    (I.card = 1 ∧ Antitone (increment (column (n+2) 3).val I)) ↔
      I ∈ ({{r n 0 (by omega)}, {r n 3 (by omega)}} : Finset (Finset (Fin (n+4)))) := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hA⟩
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
    have hx : x ∈ ({x} : Finset (Fin (n+4))) := Finset.mem_singleton_self x
    by_cases h0 : x.val = 0
    · left; rw [show x = r n 0 (by omega) from Fin.ext h0]
    by_cases h3 : x.val = 3
    · right; rw [show x = r n 3 (by omega) from Fin.ext h3]
    exfalso
    by_cases h4 : 4 ≤ x.val
    · have h1 := below_mem hA x hx (by omega)
      simp only [Finset.mem_singleton, Fin.ext_iff, r_val] at h1
      omega
    · have h1 := top_mem hA x hx (by omega)
      simp only [Finset.mem_singleton, Fin.ext_iff, r_val] at h1
      omega
  · rintro (rfl | rfl) <;>
    · refine ⟨Finset.card_singleton _, fun i j hij => ?_⟩
      have hij' : i.val ≤ j.val := hij
      simp only [increment, column, Finset.mem_singleton, Fin.ext_iff, r_val]
      split_ifs <;> (try simp only [r_val] at *) <;> omega

/-- Proposition 2.26 for `s₁₁ · s₁₁`: `s₁₁s₁₁ = -s₂₂ - s₂₁₁ + s₁₁₁₁`. -/
theorem pieri_eleven_eleven :
    schur (n+2) (column (n+2) 2) * schur (n+2) (column (n+2) 2) =
      -s22 (n+2) - s211 (n+2) + schur (n+2) (column (n+2) 4) := by
  classical
  rw [right_pieri (n+2) 2 (by omega),
    strip_sum _ (strip_column_two n)
      (fun I => (-1 : ℤ)^lowerRows (column (n+2) 2).val I •
        S (n+2) (monomial (increment (column (n+2) 2).val I) 1))
      (fun I _ _ => rfl)]
  have h01 : ({r n 0 (by omega), r n 1 (by omega)} : Finset (Fin (n+4))) ∉
      ({{r n 0 (by omega), r n 2 (by omega)}, {r n 2 (by omega), r n 3 (by omega)}} : Finset (Finset (Fin (n+4)))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h <;>
      have := congrArg (r n 1 (by omega) ∈ ·) h <;> simp [Fin.ext_iff] at this
  have h02 : ({r n 0 (by omega), r n 2 (by omega)} : Finset (Fin (n+4))) ∉
      ({{r n 2 (by omega), r n 3 (by omega)}} : Finset (Finset (Fin (n+4)))) := by
    simp only [Finset.mem_singleton]
    intro h
    have := congrArg (r n 0 (by omega) ∈ ·) h
    simp [Fin.ext_iff] at this
  rw [Finset.sum_insert h01, Finset.sum_insert h02, Finset.sum_singleton]
  rw [lowerRows_column _ _ (by omega), lowerRows_column _ _ (by omega),
    lowerRows_column _ _ (by omega)]
  rw [Finset.sum_pair (by simp [Fin.ext_iff]), Finset.sum_pair (by simp [Fin.ext_iff]),
    Finset.sum_pair (by simp [Fin.ext_iff])]
  have e1 : increment (column (n+2) 2).val {r n 0 (by omega), r n 1 (by omega)} = (twoTwo (n+2)).val := by
    funext t
    simp only [increment, column, twoTwo, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val]
    split_ifs <;> omega
  have e2 : increment (column (n+2) 2).val {r n 0 (by omega), r n 2 (by omega)} = (twoOneOne (n+2)).val := by
    funext t
    simp only [increment, column, twoOneOne, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val]
    split_ifs <;> omega
  have e3 : increment (column (n+2) 2).val {r n 2 (by omega), r n 3 (by omega)} = (column (n+2) 4).val := by
    funext t
    simp only [increment, column, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, r_val]
    split_ifs <;> omega
  rw [e1, e2, e3]
  change (-1 : ℤ) ^ 1 • s22 (n+2) + ((-1 : ℤ) ^ 1 • s211 (n+2) +
    (-1 : ℤ) ^ 0 • schur (n+2) (column (n+2) 4)) = _
  simp only [pow_one, pow_zero, neg_smul, one_smul]
  abel

/-- Proposition 2.26 for `s₁₁₁ · s₁`: `s₁₁₁s₁ = s₂₁₁ + s₁₁₁₁`. -/
theorem pieri_eleven_one_one :
    schur (n+2) (column (n+2) 3) * schur (n+2) (column (n+2) 1) =
      s211 (n+2) + schur (n+2) (column (n+2) 4) := by
  classical
  rw [right_pieri (n+2) 1 (by omega),
    strip_sum _ (strip_column_three n)
      (fun I => (-1 : ℤ)^lowerRows (column (n+2) 3).val I •
        S (n+2) (monomial (increment (column (n+2) 3).val I) 1))
      (fun I _ _ => rfl)]
  have h0 : ({r n 0 (by omega)} : Finset (Fin (n+4))) ∉ ({{r n 3 (by omega)}} : Finset (Finset (Fin (n+4)))) := by
    simp only [Finset.mem_singleton, Finset.singleton_inj, Fin.ext_iff, r_val]
    omega
  rw [Finset.sum_insert h0, Finset.sum_singleton]
  rw [lowerRows_column _ _ (by omega), lowerRows_column _ _ (by omega)]
  simp only [Finset.sum_singleton]
  have e1 : increment (column (n+2) 3).val {r n 0 (by omega)} = (twoOneOne (n+2)).val := by
    funext t
    simp only [increment, column, twoOneOne, Finset.mem_singleton, Fin.ext_iff, r_val]
    split_ifs <;> omega
  have e2 : increment (column (n+2) 3).val {r n 3 (by omega)} = (column (n+2) 4).val := by
    funext t
    simp only [increment, column, Finset.mem_singleton, Fin.ext_iff, r_val]
    split_ifs <;> omega
  rw [e1, e2]
  change (-1 : ℤ) ^ 2 • s211 (n+2) + (-1 : ℤ) ^ 0 • schur (n+2) (column (n+2) 4) = _
  simp only [even_two, Even.neg_one_pow, pow_zero, one_smul]

/-- Corrected (2.76): `s₂₂ = -ε₂₂ + ε₃₁ + 2ε₄` in every rank `a ≥ 4`. -/
theorem schur_two_two :
    s22 (n+2) = -(elementaryPoly (n+4) 2 * elementaryPoly (n+4) 2) +
      elementaryPoly (n+4) 3 * elementaryPoly (n+4) 1 + (2 : ℤ) • elementaryPoly (n+4) 4 := by
  have p1 := pieri_eleven_eleven n
  have p2 := pieri_eleven_one_one n
  rw [schur_column (n+2) 2 (by omega), schur_column (n+2) 4 (by omega)] at p1
  rw [schur_column (n+2) 3 (by omega), schur_column (n+2) 1 (by omega),
    schur_column (n+2) 4 (by omega)] at p2
  norm_num [Nat.choose] at p1 p2
  have hs : s211 (n+2) = -(elementaryPoly (n+4) 3 * elementaryPoly (n+4) 1) -
      elementaryPoly (n+4) 4 := by
    rw [eq_sub_iff_add_eq, p2]
  rw [hs] at p1
  rw [← sub_eq_zero] at p1 ⊢
  rw [← p1, two_smul]
  abel

/-- The printed `s₂₂ = ε₂₂ + ε₃₁ - 2ε₄` of (2.76) is false in every rank `a ≥ 4`. -/
theorem printed_schur_two_two_false :
    s22 (n+2) ≠ elementaryPoly (n+4) 2 * elementaryPoly (n+4) 2 +
      elementaryPoly (n+4) 3 * elementaryPoly (n+4) 1 - (2 : ℤ) • elementaryPoly (n+4) 4 := by
  intro hp
  rw [schur_two_two] at hp
  have h0 : (2 : ℤ) • (elementaryPoly (n+4) 2 * elementaryPoly (n+4) 2) -
      (4 : ℤ) • elementaryPoly (n+4) 4 = 0 := by
    rw [← sub_eq_zero.mpr hp.symm]; module
  have hc := congrArg (fun f : SkewPolynomial (n+4) => f (columnExponent (n+4) [2, 2])) h0
  dsimp only at hc
  rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
    Finsupp.coe_zero, Pi.zero_apply, ← elementaryWord_two, ← elementaryWord_one] at hc
  have hlt : toLex (columnExponent (n+4) [4]) < toLex (columnExponent (n+4) [2, 2]) := by
    refine ⟨r n 0 (by omega), fun j hj => absurd (Fin.lt_def.mp hj) (by simp), ?_⟩
    simp [columnExponent, prefixExp]
  rw [word_coeff_above (n+4) [4] (by simp) _ hlt] at hc
  exact word_coeff_unit (n+4) [2, 2] (by simp) (by linarith)

/-- The printed `s₂₂` is not correct up to a global sign either, in every rank `a ≥ 4`. -/
theorem printed_schur_two_two_false_neg :
    s22 (n+2) ≠ -(elementaryPoly (n+4) 2 * elementaryPoly (n+4) 2 +
      elementaryPoly (n+4) 3 * elementaryPoly (n+4) 1 - (2 : ℤ) • elementaryPoly (n+4) 4) := by
  intro hp
  rw [schur_two_two] at hp
  have h0 : (2 : ℤ) • (elementaryPoly (n+4) 3 * elementaryPoly (n+4) 1) = 0 := by
    rw [← sub_eq_zero.mpr hp]; module
  have hc := congrArg (fun f : SkewPolynomial (n+4) => f (columnExponent (n+4) [3, 1])) h0
  dsimp only at hc
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
    ← elementaryWord_two] at hc
  exact word_coeff_unit (n+4) [3, 1] (by simp) (by linarith)

/-! ### No naive Jacobi–Trudi identity for `α = (2,2)` -/

/-- Lexicographic comparison of exponents at a first differing row. -/
theorem lex_lt_at {N : ℕ} (a b : Fin N → ℕ) (i : Fin N) (h : ∀ j < i, a j = b j)
    (hi : a i < b i) : toLex a < toLex b := ⟨i, h, hi⟩

theorem word_zero_below (w v : List ℕ) (hw : ∀ k ∈ w, k ≤ n+4) (i : Fin (n+4))
    (h : ∀ j < i, columnExponent (n+4) w j = columnExponent (n+4) v j)
    (hi : columnExponent (n+4) w i < columnExponent (n+4) v i) :
    elementaryWord (n+4) w (columnExponent (n+4) v) = 0 :=
  word_coeff_above _ w hw _ (lex_lt_at _ _ i h hi)

/-- Remark 2.28: `s₂₂` is not an integer combination of `ε₂₂` and `ε₃₁`, in every rank
`a ≥ 4`; in particular `s₂₂ ≠ ±ε₂₂ ± ε₃₁` for every choice of signs, e.g.
`s₂₂ ≠ ±det(ε_{ᾱᵢ+j-i})`. -/
theorem schur_ne_elementary_determinant (σ₁ σ₂ : ℤ) :
    s22 (n+2) ≠ σ₁ • (elementaryPoly (n+4) 2 * elementaryPoly (n+4) 2) +
      σ₂ • (elementaryPoly (n+4) 3 * elementaryPoly (n+4) 1) := by
  intro hp
  rw [schur_two_two, ← elementaryWord_two, ← elementaryWord_two, ← elementaryWord_one] at hp
  have hev : ∀ b, (-1 - σ₁) * elementaryWord (n+4) [2, 2] b +
      (1 - σ₂) * elementaryWord (n+4) [3, 1] b + 2 * elementaryWord (n+4) [4] b = 0 := by
    intro b
    have := congrArg (fun f : SkewPolynomial (n+4) => f b) hp
    simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul] at this
    linarith
  let i0 : Fin (n+4) := ⟨0, by omega⟩
  let i1 : Fin (n+4) := ⟨1, by omega⟩
  have hlt0 : ∀ j < i0, False := fun j hj => absurd (Fin.lt_def.mp hj) (by simp [i0])
  have hlt1 : ∀ j < i1, j = i0 := fun j hj => Fin.ext (by
    have := Fin.lt_def.mp hj; simp [i1, i0] at this ⊢; omega)
  -- at `x₁²x₂²`
  have e1 := hev (columnExponent (n+4) [2, 2])
  rw [word_zero_below n [3, 1] [2, 2] (by simp) i1
      (fun j hj => by rw [hlt1 j hj]; simp [columnExponent, prefixExp, i0])
      (by simp [columnExponent, prefixExp, i1]),
    word_zero_below n [4] [2, 2] (by simp) i0 (fun j hj => (hlt0 j hj).elim)
      (by simp [columnExponent, prefixExp, i0])] at e1
  have u1 := word_coeff_unit (n+4) [2, 2] (by simp)
  have hs1 : σ₁ = -1 := by
    by_contra hne
    apply u1
    have : (-1 - σ₁) * elementaryWord (n+4) [2, 2] (columnExponent (n+4) [2, 2]) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left (by omega)
  subst hs1
  -- at `x₁²x₂x₃`
  have e2 := hev (columnExponent (n+4) [3, 1])
  rw [word_zero_below n [4] [3, 1] (by simp) i0 (fun j hj => (hlt0 j hj).elim)
      (by simp [columnExponent, prefixExp, i0])] at e2
  have u2 := word_coeff_unit (n+4) [3, 1] (by simp)
  have hs2 : σ₂ = 1 := by
    by_contra hne
    apply u2
    have : (1 - σ₂) * elementaryWord (n+4) [3, 1] (columnExponent (n+4) [3, 1]) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left (by omega)
  subst hs2
  -- at `x₁x₂x₃x₄`
  have e3 := hev (columnExponent (n+4) [4])
  have u3 := word_coeff_unit (n+4) [4] (by simp)
  apply u3; linarith

/-- Remark 2.28: `s₂₂` is not an integer combination of `h₂₂` and `h₃₁`, in every rank
`a ≥ 4`; in particular `s₂₂ ≠ ±h₂₂ ± h₃₁` for every choice of signs, e.g.
`s₂₂ ≠ ±det(h_{αᵢ+j-i})`. -/
theorem schur_ne_complete_determinant (σ₁ σ₂ : ℤ) :
    s22 (n+2) ≠ σ₁ • (completePoly (n+4) 2 * completePoly (n+4) 2) +
      σ₂ • (completePoly (n+4) 3 * completePoly (n+4) 1) := by
  intro hp
  rw [schur_two_two, complete_two_two, complete_three_one, ← elementaryWord_two,
    ← elementaryWord_two, ← elementaryWord_one, ← elementaryWord_three,
    ← elementaryWord_four] at hp
  have hev : ∀ b, (-1 - σ₁) * elementaryWord (n+4) [2, 2] b +
      (1 - σ₂) * elementaryWord (n+4) [3, 1] b + 2 * elementaryWord (n+4) [4] b -
      2 * σ₁ * elementaryWord (n+4) [2, 1, 1] b -
      (σ₁ + σ₂) * elementaryWord (n+4) [1, 1, 1, 1] b = 0 := by
    intro b
    have := congrArg (fun f : SkewPolynomial (n+4) => f b) hp
    simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul] at this
    linarith
  let i0 : Fin (n+4) := ⟨0, by omega⟩
  have hlt0 : ∀ j < i0, False := fun j hj => absurd (Fin.lt_def.mp hj) (by simp [i0])
  have z0 : ∀ w v : List ℕ, (∀ k ∈ w, k ≤ n+4) →
      columnExponent (n+4) w i0 < columnExponent (n+4) v i0 →
      elementaryWord (n+4) w (columnExponent (n+4) v) = 0 := fun w v hw hi =>
    word_zero_below n w v hw i0 (fun j hj => (hlt0 j hj).elim) hi
  -- at `x₁⁴`
  have e1 := hev (columnExponent (n+4) [1, 1, 1, 1])
  rw [z0 [2, 2] _ (by simp) (by simp [columnExponent, prefixExp, i0]),
    z0 [3, 1] _ (by simp) (by simp [columnExponent, prefixExp, i0]),
    z0 [4] _ (by simp) (by simp [columnExponent, prefixExp, i0]),
    z0 [2, 1, 1] _ (by simp) (by simp [columnExponent, prefixExp, i0])] at e1
  have u1 := word_coeff_unit (n+4) [1, 1, 1, 1] (by simp)
  have hs : σ₁ + σ₂ = 0 := by
    by_contra hne
    apply u1
    have : (σ₁ + σ₂) * elementaryWord (n+4) [1, 1, 1, 1] (columnExponent (n+4) [1, 1, 1, 1]) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hne
  -- at `x₁³x₂`
  have e2 := hev (columnExponent (n+4) [2, 1, 1])
  rw [hs, z0 [2, 2] _ (by simp) (by simp [columnExponent, prefixExp, i0]),
    z0 [3, 1] _ (by simp) (by simp [columnExponent, prefixExp, i0]),
    z0 [4] _ (by simp) (by simp [columnExponent, prefixExp, i0])] at e2
  have u2 := word_coeff_unit (n+4) [2, 1, 1] (by simp)
  have hs1 : σ₁ = 0 := by
    by_contra hne
    apply u2
    have : (2 * σ₁) * elementaryWord (n+4) [2, 1, 1] (columnExponent (n+4) [2, 1, 1]) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left (by omega)
  have hs2 : σ₂ = 0 := by omega
  subst hs1 hs2
  -- at `x₁²x₂²`
  have e3 := hev (columnExponent (n+4) [2, 2])
  let i1 : Fin (n+4) := ⟨1, by omega⟩
  have hlt1 : ∀ j < i1, j = i0 := fun j hj => Fin.ext (by
    have := Fin.lt_def.mp hj; simp [i1, i0] at this ⊢; omega)
  rw [word_zero_below n [3, 1] [2, 2] (by simp) i1
      (fun j hj => by rw [hlt1 j hj]; simp [columnExponent, prefixExp, i0])
      (by simp [columnExponent, prefixExp, i1]),
    z0 [4] _ (by simp) (by simp [columnExponent, prefixExp, i0])] at e3
  have u3 := word_coeff_unit (n+4) [2, 2] (by simp)
  apply u3; linarith

end Schur

end
end OddMath.Frontier.EKLSectionTwo

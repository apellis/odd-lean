import OddMath.PbwL4
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# General ordered-word realization in the actual skew-polynomial presentation

The source presentation is EKL, arXiv:1111.1320v1, §2.1.1, (2.1), p.3
(and (2.9), p.4), implemented in `PbwL2`. Increasing index order is the
locked convention in the sign convention. Equal indices may repeat.
This module proves realization and surjectivity, not quotient normalization
or injectivity. There is no bound on rank, word length, or multiplicity.
-/

namespace OddMath.Frontier.PbwRealization

open OddMath.SkewPolynomial

/-- Quotient evaluation of a generator list, including the empty product. -/
def word {n : ℕ} (l : List (Fin n)) : OddMath.PbwL2.Presented n :=
  (l.map (OddMath.PbwL2.q n)).prod

/-- Multiplicity vector of a word. -/
def exponents {n : ℕ} (l : List (Fin n)) : Fin n → ℕ := fun i => l.count i

@[simp] theorem exponents_nil (n : ℕ) : exponents ([] : List (Fin n)) = 0 := by
  funext i
  simp [exponents]

theorem exponents_cons {n : ℕ} (i : Fin n) (l : List (Fin n)) :
    exponents (i :: l) = expSingle i + exponents l := by
  funext j
  by_cases h : i = j
  · subst j; simp [exponents, expSingle, Nat.add_comm]
  · simp [exponents, expSingle, h]

/-- A least index crosses none of the letters in the remaining list. -/
theorem crossingCount_head {n : ℕ} (i : Fin n) (l : List (Fin n))
    (h : ∀ j ∈ l, i ≤ j) : OddMath.crossingCount (expSingle i) (exponents l) = 0 := by
  induction l with
  | nil => simp [exponents_nil, crossingCount_zero_right]
  | cons j l ih =>
    rw [exponents_cons, OddMath.crossingCount_add_right, crossingCount_expSingle,
      if_neg (not_lt.mpr (h j (by simp))), ih (fun k hk => h k (by simp [hk]))]

/-- Every nondecreasing word evaluates to its multiplicity monomial with sign +1. -/
theorem Phi_word_of_sorted {n : ℕ} (l : List (Fin n)) (h : l.Sorted (· ≤ ·)) :
    OddMath.PbwL3.Phi n (word l) = monomial (exponents l) 1 := by
  induction l with
  | nil =>
    simp only [word, List.map_nil, List.prod_nil, map_one, exponents_nil]
    rfl
  | cons i l ih =>
    obtain ⟨hi, ht⟩ := List.pairwise_cons.mp h
    have hs : OddMath.skewSign (expSingle i) (exponents l) = 1 := by
      unfold OddMath.skewSign
      rw [crossingCount_head i l hi, pow_zero]
    change OddMath.PbwL3.Phi n (OddMath.PbwL2.q n i * word l) = _
    rw [map_mul, OddMath.PbwL3.Phi_q, ih ht, exponents_cons]
    change OddMath.SkewPolynomial.mul (monomial (expSingle i) 1)
      (monomial (exponents l) 1) = _
    rw [mul_monomial, hs]
    norm_num

/-- A canonical nondecreasing list with the prescribed repetitions. -/
def orderedList {n : ℕ} (a : Fin n → ℕ) : List (Fin n) :=
  ((List.finRange n).flatMap (fun i => List.replicate (a i) i)).mergeSort
    (fun i j => decide (i ≤ j))

theorem orderedList_sorted {n : ℕ} (a : Fin n → ℕ) :
    (orderedList a).Sorted (· ≤ ·) :=
  List.sorted_mergeSort' (· ≤ ·) _

/-- Every exponent vector, not merely square-free vectors, is realized. -/
theorem exponents_orderedList {n : ℕ} (a : Fin n → ℕ) :
    exponents (orderedList a) = a := by
  funext i
  unfold exponents orderedList
  rw [(List.mergeSort_perm _ _).count_eq, List.count_flatMap]
  have h : (List.map (List.count i ∘ (fun j => List.replicate (a j) j))
      (List.finRange n)).sum = ∑ j : Fin n, if j = i then a j else 0 := by
    rw [← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]
    congr 1
    funext j
    simp [Function.comp_def, List.count_replicate]
  rw [h]
  simp

/-- Uniform ordered-word realization of each unit-coefficient monomial. -/
theorem exists_ordered_word {n : ℕ} (a : Fin n → ℕ) :
    ∃ l : List (Fin n), l.Sorted (· ≤ ·) ∧ exponents l = a ∧
      OddMath.PbwL3.Phi n (word l) = monomial a 1 := by
  refine ⟨orderedList a, orderedList_sorted a, exponents_orderedList a, ?_⟩
  rw [Phi_word_of_sorted _ (orderedList_sorted a), exponents_orderedList]

/-- Integer coefficients lift by scalar multiplication in the actual quotient. -/
theorem Phi_smul_word {n : ℕ} (a : Fin n → ℕ) (c : ℤ) :
    OddMath.PbwL3.Phi n (c • word (orderedList a)) = monomial a c := by
  rw [map_zsmul, Phi_word_of_sorted _ (orderedList_sorted a), exponents_orderedList,
    ← OddMath.PbwL4.monomial_smul]

/-- Surjectivity of the presentation-to-model map, in all ranks and degrees.
This does not assert injectivity or quotient-side normal ordering. -/
theorem Phi_surjective (n : ℕ) : Function.Surjective (OddMath.PbwL3.Phi n) := by
  intro f
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | single a c => exact ⟨c • word (orderedList a), Phi_smul_word a c⟩

end OddMath.Frontier.PbwRealization

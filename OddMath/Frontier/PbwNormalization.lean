import OddMath.PbwL2
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# General quotient normal ordering

The carrier is `PbwL2.Presented n`, the integer free algebra modulo only the
anticommutators of DISTINCT generators. Canonical order is increasing index.
Source: EKL arXiv:1111.1320v1, §2.1.1, (2.1); the sign convention.
No model map or surjectivity result is used.
-/

namespace OddMath.Frontier.PbwNormalization

open PbwL2

variable {n : ℕ}

/-- Evaluate a word in the actual presented quotient. -/
def word (w : List (Fin n)) : Presented n := (w.map (q n)).prod

@[simp] theorem word_nil : word ([] : List (Fin n)) = 1 := rfl

@[simp] theorem word_cons (i : Fin n) (w : List (Fin n)) :
    word (i :: w) = q n i * word w := rfl

@[simp] theorem word_append (u v : List (Fin n)) :
    word (u ++ v) = word u * word v := by
  simp [word, List.map_append, List.prod_append]

/-- Increasing list with each index repeated by its multiplicity. -/
def canonicalWord (a : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (a i) i)

/-- Canonical ordered monomial in the quotient, not in the model. -/
def orderedMonomial (a : Fin n → ℕ) : Presented n := word (canonicalWord a)

/-- The number of strict adjacent crossings made by ordered insertion. -/
def insertCrossings (i : Fin n) : List (Fin n) → ℕ
  | [] => 0
  | j :: w => if i ≤ j then 0 else insertCrossings i w + 1

/-- Total actual adjacent crossings made by insertion sort. -/
def sortCrossings : List (Fin n) → ℕ
  | [] => 0
  | i :: w => sortCrossings w + insertCrossings i (w.insertionSort (· ≤ ·))

/-- Moving a generator through precisely the strict inversions adds one minus
sign per crossing; equal indices stop insertion and are never swapped. -/
theorem word_insert (i : Fin n) (w : List (Fin n)) :
    q n i * word w = (-1 : ℤ) ^ insertCrossings i w •
      word (w.orderedInsert (· ≤ ·) i) := by
  induction w with
  | nil => simp [List.orderedInsert, insertCrossings]
  | cons j w ih =>
    by_cases h : i ≤ j
    · simp [List.orderedInsert, insertCrossings, h]
    · have hne : i ≠ j := fun e => h (e ▸ le_refl j)
      simp only [List.orderedInsert, insertCrossings, if_neg h, word_cons]
      rw [← mul_assoc, rel_anticommute n i j hne, neg_mul, mul_assoc, ih]
      rw [mul_smul_comm, pow_succ, mul_smul]
      simp only [neg_one_smul, smul_neg]

/-- Every word reduces in the quotient to its sorted word with the actual
insertion-sort crossing sign. No degree or strand bound is present. -/
theorem word_sort (w : List (Fin n)) :
    word w = (-1 : ℤ) ^ sortCrossings w • word (w.insertionSort (· ≤ ·)) := by
  induction w with
  | nil => simp [List.insertionSort, sortCrossings]
  | cons i w ih =>
    simp only [word_cons, List.insertionSort, sortCrossings]
    rw [ih, mul_smul_comm, word_insert, smul_smul, ← pow_add]

/-- Canonical words are weakly increasing, retaining all repeated indices. -/
theorem canonicalWord_sorted (a : Fin n → ℕ) :
    (canonicalWord a).Sorted (· ≤ ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact List.pairwise_replicate.mpr (Or.inr (le_refl i))
  · apply (List.pairwise_le_finRange n).imp
    intro i j hij x hx y hy
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hy
    exact hij

private theorem count_repeated (a : Fin n → ℕ) (i : Fin n) (l : List (Fin n)) :
    (l.flatMap (fun j => List.replicate (a j) j)).count i = l.count i * a i := by
  induction l with
  | nil => simp
  | cons j l ih =>
    by_cases h : j = i
    · subst j
      simp [ih, Nat.add_mul, Nat.add_comm]
    · simp [List.flatMap_cons, List.count_append, List.count_replicate, h, ih]

@[simp] theorem canonicalWord_count (a : Fin n → ℕ) (i : Fin n) :
    (canonicalWord a).count i = a i := by
  rw [canonicalWord, count_repeated, List.count_finRange, one_mul]

/-- Sorting produces exactly the fixed increasing repetition-list, not merely
an unspecified permutation with the same multiplicities. -/
theorem sort_eq_canonicalWord (w : List (Fin n)) :
    w.insertionSort (· ≤ ·) = canonicalWord (fun i => w.count i) := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · apply List.perm_iff_count.mpr
    intro i
    rw [canonicalWord_count]
    exact (List.perm_insertionSort (· ≤ ·) w).count_eq i
  · exact List.sorted_insertionSort (· ≤ ·) w
  · exact canonicalWord_sorted _

/-- Arbitrary-length normal ordering in the presented algebra. -/
theorem word_normalize (w : List (Fin n)) :
    word w = (-1 : ℤ) ^ sortCrossings w • orderedMonomial (fun i => w.count i) := by
  simpa only [sort_eq_canonicalWord, orderedMonomial] using word_sort w

/-- The normalization coefficient is a genuine sign, not an arbitrary integer. -/
theorem word_eq_signed_orderedMonomial (w : List (Fin n)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      word w = ε • orderedMonomial (fun i => w.count i) :=
  ⟨(-1) ^ sortCrossings w, neg_one_pow_eq_or ℤ _, word_normalize w⟩

/-- The integer span of the canonical quotient monomials. -/
def orderedSpan (n : ℕ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (@orderedMonomial n))

/-- Every generator word belongs to the ordered span. -/
theorem word_mem_orderedSpan (w : List (Fin n)) : word w ∈ orderedSpan n := by
  rw [word_normalize]
  exact (orderedSpan n).smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Multiplication preserves this span, by concatenation and word normalization. -/
theorem orderedSpan_mul_mem {x y : Presented n}
    (hx : x ∈ orderedSpan n) (hy : y ∈ orderedSpan n) : x * y ∈ orderedSpan n := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact word_append (canonicalWord a) (canonicalWord b) ▸
      word_mem_orderedSpan (canonicalWord a ++ canonicalWord b)
  | zero_left => simpa only [zero_mul] using (orderedSpan n).zero_mem
  | zero_right => simpa only [mul_zero] using (orderedSpan n).zero_mem
  | add_left x y z _ _ _ h₁ h₂ =>
    simpa only [add_mul] using (orderedSpan n).add_mem h₁ h₂
  | add_right x y z _ _ _ h₁ h₂ =>
    simpa only [mul_add] using (orderedSpan n).add_mem h₁ h₂
  | smul_left r x y _ _ h =>
    simpa only [smul_mul_assoc] using (orderedSpan n).smul_mem r h
  | smul_right r x y _ _ h =>
    simpa only [mul_smul_comm] using (orderedSpan n).smul_mem r h

/-- Every element of the actual quotient lies in the ordered span. The proof
uses free-algebra induction and quotient surjectivity, NOT model surjectivity. -/
theorem mem_orderedSpan (x : Presented n) : x ∈ orderedSpan n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using FreeAlgebra.induction with
  | grade0 r =>
    have h := (orderedSpan n).smul_mem r (word_mem_orderedSpan ([] : List (Fin n)))
    simpa [zsmul_eq_mul] using h
  | grade1 i =>
    simpa only [word_cons, word_nil, mul_one] using word_mem_orderedSpan [i]
  | mul a b ha hb =>
    rw [map_mul]
    exact orderedSpan_mul_mem ha hb
  | add a b ha hb =>
    rw [map_add]
    exact (orderedSpan n).add_mem ha hb

/-- General quotient-side spanning, including zero variables and all degrees. -/
theorem orderedSpan_eq_top (n : ℕ) : orderedSpan n = ⊤ := by
  apply top_unique
  intro x _
  exact mem_orderedSpan x

/-- Explicit finite-support quotient expansion. Existence only: uniqueness
requires the model's coordinate independence and is not assumed here. -/
theorem exists_ordered_expansion (x : Presented n) :
    ∃ c : (Fin n → ℕ) →₀ ℤ, c.sum (fun a r => r • orderedMonomial a) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (mem_orderedSpan x)

end OddMath.Frontier.PbwNormalization

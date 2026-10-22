/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Long products in a graded ring with a nilpotent pairing ideal

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. There one needs that a degree-zero corner of a tensor product of two graded rings
with local degree-zero parts is again local. This file isolates the combinatorial core.

Let `B g ⊆ R` (`g ∈ Γ`) be multiplicative subsets of a ring (`B g * B h ⊆ B (g + h)`,
`1 ∈ B 0`), zero outside a finite window `Win`, and let `N ⊆ B 0` be absorbing on the right for
`B 0`, with all products of `m` elements of `N` zero and `B g * B (-g) ⊆ N` for `g ≠ 0`. Call an
element of `B g` *small* if `g ≠ 0` or it lies in `N`. Then every product of more than
`#Win * m - 1` small homogeneous elements is zero (`prod_eq_zero_of_walk`).

The proof walks through the partial degree sums: if one leaves `Win` the product vanishes;
otherwise by pigeonhole some value is visited `m + 1` times, and each segment between two visits
has degree zero and lies in `N`.
-/

namespace OddMath.SKM.GradedWalk

open Finset

variable {Γ R : Type*} [AddCommGroup Γ] [Ring R]

/-- The product `x i * x (i + 1) * ⋯ * x (j - 1)` (empty if `j ≤ i`). -/
def seg (x : ℕ → R) (i j : ℕ) : R := ((List.range' i (j - i)).map x).prod

/-- The partial degree sum `g 0 + ⋯ + g (j - 1)`. -/
def psum (g : ℕ → Γ) (j : ℕ) : Γ := ∑ t ∈ range j, g t

theorem seg_self (x : ℕ → R) (i : ℕ) : seg x i i = 1 := by simp [seg]

theorem seg_mul {x : ℕ → R} {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    seg x i j * seg x j l = seg x i l := by
  unfold seg
  rw [← List.prod_append, ← List.map_append]
  congr 2
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hjl
  simp only [Nat.add_sub_cancel_left, show i + a + b - i = a + b by omega]
  exact List.range'_append_1

theorem seg_succ_right (x : ℕ → R) {i j : ℕ} (hij : i ≤ j) :
    seg x i (j + 1) = seg x i j * x j := by
  rw [← seg_mul hij (Nat.le_succ j)]
  simp [seg]

theorem seg_succ_left (x : ℕ → R) {i j : ℕ} (hij : i < j) :
    seg x i j = x i * seg x (i + 1) j := by
  rw [← seg_mul (Nat.le_succ i) hij]
  simp [seg]

variable (B : Γ → Set R) (N : Set R) (Win : Finset Γ) (m : ℕ)

/-- Hypotheses of the walk lemma. -/
structure Walk : Prop where
  one_mem : (1 : R) ∈ B 0
  mul_mem : ∀ {g h : Γ} {x y : R}, x ∈ B g → y ∈ B h → x * y ∈ B (g + h)
  eq_zero : ∀ {g : Γ} {x : R}, g ∉ Win → x ∈ B g → x = 0
  mul_mem_N : ∀ {x y : R}, x ∈ N → y ∈ B 0 → x * y ∈ N
  pair_mem_N : ∀ {g : Γ} {x y : R}, g ≠ 0 → x ∈ B g → y ∈ B (-g) → x * y ∈ N
  nil : ∀ l : List R, l.length = m → (∀ y ∈ l, y ∈ N) → l.prod = 0

variable {B N Win m}

theorem seg_mem (hW : Walk B N Win m) {g : ℕ → Γ} {x : ℕ → R} {L : ℕ}
    (hx : ∀ t < L, x t ∈ B (g t)) {i j : ℕ} (hij : i ≤ j) (hjL : j ≤ L) :
    seg x i j ∈ B (psum g j - psum g i) := by
  induction j, hij using Nat.le_induction with
  | base => simpa [seg_self] using hW.one_mem
  | succ j hij ih =>
    rw [seg_succ_right x hij]
    have := hW.mul_mem (ih (by omega)) (hx j (by omega))
    convert this using 2
    simp only [psum, sum_range_succ]
    abel

theorem seg_mem_N (hW : Walk B N Win m) {g : ℕ → Γ} {x : ℕ → R} {L : ℕ}
    (hx : ∀ t < L, x t ∈ B (g t) ∧ (g t ≠ 0 ∨ x t ∈ N)) {i j : ℕ} (hij : i < j) (hjL : j ≤ L)
    (hs : psum g i = psum g j) : seg x i j ∈ N := by
  rw [seg_succ_left x hij]
  have hrest := seg_mem hW (fun t ht => (hx t ht).1) (Nat.succ_le_of_lt hij) hjL
  have hdeg : psum g j - psum g (i + 1) = -g i := by
    rw [← hs]; simp only [psum, sum_range_succ]; abel
  rw [hdeg] at hrest
  by_cases hg : g i = 0
  · rw [hg, neg_zero] at hrest
    rcases (hx i (by omega)).2 with h | h
    · exact absurd hg h
    · exact hW.mul_mem_N h hrest
  · exact hW.pair_mem_N hg (hx i (by omega)).1 hrest

theorem seg_telescope (x : ℕ → R) (f : ℕ → ℕ) :
    ∀ k : ℕ, (∀ t < k, f t ≤ f (t + 1)) →
      f 0 ≤ f k ∧ seg x (f 0) (f k) = ((List.range k).map fun t => seg x (f t) (f (t + 1))).prod
  | 0, _ => by simp [seg_self]
  | k + 1, hf => by
    obtain ⟨h0, ih⟩ := seg_telescope x f k (fun t ht => hf t (by omega))
    have hk := hf k (by omega)
    refine ⟨h0.trans hk, ?_⟩
    rw [List.range_succ, List.map_append, List.prod_append, ← ih, List.map_singleton,
      List.prod_singleton, seg_mul h0 hk]

/-- **The walk lemma.** A product of `L` small homogeneous elements vanishes as soon as
`#Win * m < L + 1`. -/
theorem prod_eq_zero_of_walk [DecidableEq Γ] (hW : Walk B N Win m) {g : ℕ → Γ} {x : ℕ → R}
    {L : ℕ} (hx : ∀ t < L, x t ∈ B (g t) ∧ (g t ≠ 0 ∨ x t ∈ N)) (hL : #Win * m < L + 1) :
    ((List.range L).map x).prod = 0 := by
  have hseg : ((List.range L).map x).prod = seg x 0 L := by simp [seg, List.range_eq_range']
  rw [hseg]
  have hB := fun t ht => (hx t ht).1
  by_cases hout : ∃ j ≤ L, psum g j ∉ Win
  · obtain ⟨j, hj, hjw⟩ := hout
    have h0 : seg x 0 j = 0 := by
      refine hW.eq_zero (g := psum g j) hjw ?_
      simpa [psum] using seg_mem hW hB (Nat.zero_le j) hj
    rw [← seg_mul (Nat.zero_le j) hj, h0, zero_mul]
  push Not at hout
  have hmaps : ∀ j ∈ range (L + 1), psum g j ∈ Win := fun j hj =>
    hout j (Nat.lt_succ_iff.mp (mem_range.mp hj))
  obtain ⟨v, -, hv⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (by simpa using hL)
  set S := {j ∈ range (L + 1) | psum g j = v} with hS
  let p := S.orderEmbOfFin rfl
  let q : ℕ → ℕ := fun t => if h : t < #S then p ⟨t, h⟩ else 0
  have hqS : ∀ t ≤ m, q t ∈ S := fun t ht => by
    simp only [q, (show t < #S by omega), ↓reduceDIte]
    exact S.orderEmbOfFin_mem rfl _
  have hqL : ∀ t ≤ m, q t ≤ L := fun t ht => by
    have := hqS t ht
    rw [hS, mem_filter, mem_range] at this
    omega
  have hqv : ∀ t ≤ m, psum g (q t) = v := fun t ht => by
    have := hqS t ht
    rw [hS, mem_filter] at this
    exact this.2
  have hqlt : ∀ t < m, q t < q (t + 1) := fun t ht => by
    simp only [q, (show t < #S by omega), (show t + 1 < #S by omega), ↓reduceDIte]
    exact p.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self t))
  obtain ⟨hq0m, htel⟩ := seg_telescope x q m (fun t ht => (hqlt t ht).le)
  have hmid : seg x (q 0) (q m) = 0 := by
    rw [htel]
    refine hW.nil _ (by simp) ?_
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    have ht := List.mem_range.mp ht
    exact seg_mem_N hW hx (hqlt t ht) (hqL _ (by omega))
      ((hqv t ht.le).trans (hqv (t + 1) (by omega)).symm)
  rw [← seg_mul (Nat.zero_le (q 0)) (hq0m.trans (hqL m le_rfl)),
    ← seg_mul hq0m (hqL m le_rfl), hmid, zero_mul, mul_zero]

end OddMath.SKM.GradedWalk

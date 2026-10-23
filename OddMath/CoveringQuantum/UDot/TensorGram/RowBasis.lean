/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Row bases of graded symmetric Gram matrices

For a symmetric matrix `G` over a field whose entries vanish between different grades, a subset
`W` of indices whose rows form a basis of the row space has two properties: every row is a
combination of rows in `W` of the same grade, and the principal submatrix on `W` is invertible.
This is used to choose finitely many words spanning a half algebra modulo the radical of its
form (Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1 at `π = -1`). The argument is ours.

We also record that a matrix which is triangular with respect to a height function and has
ones on the diagonal has determinant one.
-/

namespace OddMath.CoveringQuantum.UDot.RowBasis

open Matrix

variable {K T κ : Type*} [Field K] [Fintype T] [DecidableEq T]

/-- A row basis of a graded symmetric matrix. -/
theorem exists_rowBasis (G : Matrix T T K) (hG : ∀ a b, G a b = G b a) (g : T → κ)
    (hg : ∀ a b, g a ≠ g b → G a b = 0) :
    ∃ W : Finset T,
      (∀ a, ∃ c : T → K, (∀ w, c w ≠ 0 → w ∈ W ∧ g w = g a) ∧
        ∀ b, G a b = ∑ w ∈ W, c w * G w b) ∧
      (G.submatrix ((↑) : W → T) ((↑) : W → T)).det ≠ 0 := by
  classical
  obtain ⟨ι, f, hf, hspan, hli⟩ := exists_linearIndependent' K (fun a : T ↦ G a)
  let W : Finset T := Finset.univ.filter (· ∈ Set.range f)
  have hW : ∀ w, w ∈ W ↔ w ∈ Set.range f := by simp [W]
  -- every row is a combination of the rows indexed by `W`
  have hrow : ∀ a, ∃ c : T → K, (∀ w, c w ≠ 0 → w ∈ W) ∧ G a = ∑ w ∈ W, c w • G w := by
    intro a
    have ha : G a ∈ Submodule.span K (Set.range (fun w : W ↦ G w)) := by
      have h1 : G a ∈ Submodule.span K (Set.range (fun a : T ↦ G a)) :=
        Submodule.subset_span ⟨a, rfl⟩
      rw [← hspan] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨f i, (hW _).2 ⟨i, rfl⟩⟩, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ha
    refine ⟨fun w ↦ if h : w ∈ W then c ⟨w, h⟩ else 0, ?_, ?_⟩
    · intro w hw
      by_contra h
      exact hw (dite_eq_right_iff.mpr fun h' ↦ absurd h' h)
    · rw [← hc, ← Finset.sum_coe_sort W]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp
  refine ⟨W, ?_, ?_⟩
  · intro a
    obtain ⟨c, hcW, hc⟩ := hrow a
    refine ⟨fun w ↦ if g w = g a then c w else 0, ?_, ?_⟩
    · intro w hw
      by_cases h : g w = g a
      · simp only [h, ite_true] at hw
        exact ⟨hcW w hw, h⟩
      · simp [h] at hw
    · intro b
      by_cases hab : g b = g a
      · have hb := congrFun hc b
        rw [Finset.sum_apply] at hb
        rw [hb]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        by_cases h : g w = g a
        · simp [h]
        · simp only [h, ite_false, zero_mul, Pi.smul_apply, smul_eq_mul]
          rw [hg w b (fun h' ↦ h (h'.trans hab)), mul_zero]
      · rw [hg a b (fun h' ↦ hab h'.symm)]
        refine (Finset.sum_eq_zero fun w _ ↦ ?_).symm
        by_cases h : g w = g a
        · simp only [h, ite_true]
          rw [hg w b (fun h' ↦ hab (h'.symm.trans h)), mul_zero]
        · simp [h]
  · intro hdet
    obtain ⟨k, hk0, hk⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
    -- the combination `∑ k_w G_w` of rows vanishes
    have hvan : ∑ w : W, k w • G w = 0 := by
      funext b
      rw [Finset.sum_apply, Pi.zero_apply]
      obtain ⟨c, hcW, hc⟩ := hrow b
      have hcol : ∀ w : W, G w b = ∑ w' ∈ W, c w' * G w' w := by
        intro w
        rw [hG, congrFun hc w, Finset.sum_apply]
        simp
      calc ∑ w : W, (k w • G w) b = ∑ w : W, k w * ∑ w' ∈ W, c w' * G w' w := by
            simp [hcol]
        _ = ∑ w' ∈ W, c w' * ∑ w : W, G w' w * k w := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun w' _ ↦ Finset.sum_congr rfl fun w _ ↦ by ring
        _ = 0 := by
            refine Finset.sum_eq_zero fun w' hw' ↦ ?_
            have := congrFun hk ⟨w', hw'⟩
            simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at this
            rw [this, mul_zero]
    -- linear independence of the rows indexed by `W`
    have hliW : LinearIndependent K (fun w : W ↦ G w) := by
      have e : ∀ w : W, ∃ i, f i = w := fun w ↦ (hW w).1 w.2
      choose j hj using e
      have hj' : Function.Injective j := by
        intro w w' h
        exact Subtype.ext (by rw [← hj w, ← hj w', h])
      have := hli.comp j hj'
      convert this using 1
      funext w
      simp [Function.comp, hj]
    exact hk0 (Fintype.linearIndependent_iff.mp hliW k hvan |> funext)

/-- A matrix with ones on the diagonal whose off-diagonal entries vanish unless the height
strictly drops has determinant one. -/
theorem det_eq_one_of_triangular {R : Type*} [CommRing R] (M : Matrix T T R) (h : T → ℕ)
    (hdiag : ∀ i, M i i = 1) (hlow : ∀ i j, i ≠ j → M i j ≠ 0 → h j < h i) : M.det = 1 := by
  classical
  have hM : M.BlockTriangular (OrderDual.toDual ∘ h) := by
    intro i j hij
    by_contra hne
    have hij' : h i < h j := hij
    by_cases e : i = j
    · subst e; exact lt_irrefl _ hij'
    · exact lt_asymm (hlow i j e hne) hij'
  rw [hM.det]
  refine Finset.prod_eq_one fun a _ ↦ ?_
  have : M.toSquareBlock (OrderDual.toDual ∘ h) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [toSquareBlock, toSquareBlockProp, Matrix.one_apply, Subtype.mk.injEq]
    by_cases e : i = j
    · subst e; simp [hdiag]
    · simp only [e, ite_false]
      by_contra hne
      have hi' : h i = h j := by
        simp only [Function.comp_apply] at hi hj
        exact OrderDual.toDual.injective (hi.trans hj.symm)
      exact lt_irrefl (h j) (hi' ▸ hlow i j e hne)
  rw [this, det_one]

end OddMath.CoveringQuantum.UDot.RowBasis

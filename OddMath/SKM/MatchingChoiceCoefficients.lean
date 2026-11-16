import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Algebra.Algebra.Basic

import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.Finset.Max

/-! # Finite right-coefficient transitions

Coefficient bookkeeping for the signed matching-choice comparison.
Multiplication of abstract coefficients is not assumed commutative.
-/
noncomputable section
namespace OddMath.SKM.MatchingTransition
open scoped BigOperators
variable {k R A B : Type*} [CommRing k] [Ring R] [Algebra k R]

/-- Multiply every entry of a finite column on the right by its input coefficient. -/
def rightColumn (v : B →₀ R) : R →ₗ[k] (B →₀ R) where
  toFun p := v.mapRange (fun d => d * p) (zero_mul p)
  map_add' p q := by ext i; simp [mul_add]
  map_smul' r p := by ext i; simp

@[simp] theorem rightColumn_apply (v : B →₀ R) (p : R) (i : B) :
    rightColumn (k := k) v p i = v i * p := rfl

@[simp] theorem rightColumn_zero (p : R) :
    rightColumn (k := k) (0 : B →₀ R) p = 0 := by ext i; simp

theorem rightColumn_add (v w : B →₀ R) (p : R) :
    rightColumn (k := k) (v + w) p = rightColumn (k := k) v p + rightColumn (k := k) w p := by
  ext i
  simp [add_mul]

@[simp] theorem rightColumn_single (i : B) (d p : R) :
    rightColumn (k := k) (Finsupp.single i d) p = Finsupp.single i (d * p) := by
  classical
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Finsupp.single_eq_of_ne h]

/-- Extend the chosen unit columns; do not choose a new preimage for each input. -/
def transition (v : A → B →₀ R) : (A →₀ R) →ₗ[k] (B →₀ R) :=
  Finsupp.lsum k (fun i => rightColumn (k := k) (v i))

@[simp] theorem transition_single (v : A → B →₀ R) (i : A) (p : R) :
    transition (k := k) v (Finsupp.single i p) = rightColumn (k := k) (v i) p :=
  Finsupp.lsum_single k _ i p

theorem transition_apply (v : A → B →₀ R) (f : A →₀ R) (i : B) :
    transition (k := k) v f i = ∑ j ∈ f.support, v j i * f j := by
  classical
  simp [transition, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply]
/-- Finite columns with a nonzero-reflecting diagonal and strictly smaller
crossing/dot lower terms detect every finite relation. -/
theorem eq_zero_of_transition (e : A → B) (crossings dots : A → ℕ)
    (v : A → B →₀ R)
    (htri : ∀ i j, i ≠ j → v j (e i) ≠ 0 →
      crossings i < crossings j ∨ (crossings i = crossings j ∧ dots i < dots j))
    (hdiag : ∀ i p, v i (e i) * p = 0 → p = 0)
    (f : A →₀ R) (hf : transition (k := k) v f = 0) : f = 0 := by
  classical
  by_contra hne
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image f.support crossings
    (Finsupp.support_nonempty_iff.mpr hne)
  let S := f.support.filter fun j => crossings j = crossings a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  obtain ⟨i, hi, hdot⟩ := Finset.exists_max_image S dots hS
  have his := (Finset.mem_filter.mp hi).1
  have hic := (Finset.mem_filter.mp hi).2
  have hz := congrArg (fun x : B →₀ R => x (e i)) hf
  rw [transition_apply, Finsupp.zero_apply, Finset.sum_eq_single i] at hz
  · exact (Finsupp.mem_support_iff.mp his) (hdiag i (f i) hz)
  · intro j hj hji
    have hjc : crossings j ≤ crossings i := by simpa [hic] using hmax j hj
    have hz : v j (e i) = 0 := by
      by_contra hv
      rcases htri i j (Ne.symm hji) hv with hc | ⟨hc, hd⟩
      · exact (not_lt_of_ge hjc) hc
      · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨hj, hc.symm.trans hic⟩
        exact (not_lt_of_ge (hdot j hjS)) hd
    rw [hz, zero_mul]
  · intro hnot
    exact False.elim (hnot his)

theorem transition_injective (e : A → B) (crossings dots : A → ℕ)
    (v : A → B →₀ R)
    (htri : ∀ i j, i ≠ j → v j (e i) ≠ 0 →
      crossings i < crossings j ∨ (crossings i = crossings j ∧ dots i < dots j))
    (hdiag : ∀ i p, v i (e i) * p = 0 → p = 0) :
    Function.Injective (transition (k := k) v) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply eq_zero_of_transition (k := k) e crossings dots v htri hdiag
  rw [map_sub, hfg, sub_self]

/-- Lexicographic crossing/open-dot descent is well founded even though a
crossing drop may increase the dot count without bound. -/
theorem crossingDot_wellFounded (crossings dots : A → ℕ) :
    WellFounded (fun i j => crossings i < crossings j ∨
      (crossings i = crossings j ∧ dots i < dots j)) := by
  have h := InvImage.wf (fun i : A => (crossings i, dots i))
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  change WellFounded (fun i j : A => Prod.Lex (fun m n : ℕ => m < n)
    (fun m n : ℕ => m < n) (crossings i, dots i) (crossings j, dots j)) at h
  simpa only [Prod.lex_def] using h

/-- A well-founded finite triangular transition with right-invertible leading
entries is surjective. Lower terms need no uniform bound on their depth. -/
theorem transition_surjective (e : A ≃ B) (rel : A → A → Prop)
    (hwf : WellFounded rel) (v : A → B →₀ R) (d : A → R)
    (htri : ∀ i j, i ≠ j → v j (e i) ≠ 0 → rel i j)
    (hdiag : ∀ i, v i (e i) * d i = 1) :
    Function.Surjective (transition (k := k) v) := by
  classical
  let T := transition (k := k) v
  have hs : ∀ i : A, ∀ p : R, Finsupp.single (e i) p ∈ T.range := by
    intro i
    induction i using hwf.induction with
    | h i ih =>
      intro p
      let x := Finsupp.single i (d i * p)
      let err := T x - Finsupp.single (e i) p
      have herrdiag : err (e i) = 0 := by
        simp only [err, x, T, Finsupp.sub_apply, transition_single, rightColumn_apply,
          Finsupp.single_eq_same, ← mul_assoc, hdiag, one_mul, sub_self]
      have herr : err ∈ T.range := by
        rw [← Finsupp.sum_single err]
        apply Submodule.sum_mem
        intro b hb
        have hne : b ≠ e i := by
          intro h
          subst b
          exact Finsupp.mem_support_iff.mp hb herrdiag
        have hv : v i b ≠ 0 := by
          intro hz
          have he : err b = 0 := by
            simp only [err, x, T, Finsupp.sub_apply, transition_single, rightColumn_apply,
              hz, zero_mul, Finsupp.single_eq_of_ne hne, sub_self]
          exact Finsupp.mem_support_iff.mp hb he
        have hrel : rel (e.symm b) i := htri (e.symm b) i
          (fun h => hne (by simpa using congrArg e h)) (by simpa using hv)
        simpa using ih (e.symm b) hrel (err b)
      have hx : T x ∈ T.range := ⟨x, rfl⟩
      have h := Submodule.sub_mem T.range hx herr
      simpa only [err, sub_sub_cancel] using h
  intro f
  have hf : f ∈ T.range := by
    rw [← Finsupp.sum_single f]
    apply Submodule.sum_mem
    intro b hb
    simpa using hs (e.symm b) (f b)
  exact hf

end OddMath.SKM.MatchingTransition

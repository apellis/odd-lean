import StringDiagrams.Super.Envelope
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Ordered finite recurrences used for the separated mixed-mate expansions.

The source dot-slide and the parity-line comparisons are separate inputs.
This proves the algebraic expansion and uniqueness once the ordered recurrence
is known, in any preadditive category; it does not construct an SKM action.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators

namespace NonVacuity.MixedMateRecurrence

variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

/-- Iterate an affine two-sided recurrence without exchanging any factors. -/
theorem expansion_with_tail (s : End X) (t : End Y) (b f : X ⟶ Y)
    (h : f = b + s ≫ f ≫ t) (n : ℕ) :
    f = (∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j)) +
      (s ^ n) ≫ f ≫ (t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      f = (∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j)) +
          (s ^ n) ≫ f ≫ (t ^ n) := ih
      _ = (∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j)) +
          (s ^ n) ≫ (b + s ≫ f ≫ t) ≫ (t ^ n) := by rw [← h]
      _ = (∑ j ∈ Finset.range (n + 1), (s ^ j) ≫ b ≫ (t ^ j)) +
          (s ^ (n + 1)) ≫ f ≫ (t ^ (n + 1)) := by
        simp only [Finset.sum_range_succ, Preadditive.comp_add, Preadditive.add_comp,
          pow_succ' s n, pow_succ t n, End.mul_def, Category.assoc, add_assoc]

/-- Either nilpotent side kills the remainder of the ordered expansion. -/
theorem expansion (s : End X) (t : End Y) (b f : X ⟶ Y)
    (h : f = b + s ≫ f ≫ t) (n : ℕ)
    (hn : s ^ n = 0 ∨ t ^ n = 0) :
    f = ∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j) := by
  have he := expansion_with_tail s t b f h n
  rcases hn with hs | ht
  · simpa [hs] using he
  · simpa [ht] using he

/-- Hence the projected dot-slide can have at most one solution. -/
theorem unique (s : End X) (t : End Y) (b f g : X ⟶ Y)
    (hf : f = b + s ≫ f ≫ t) (hg : g = b + s ≫ g ≫ t)
    (n : ℕ) (hn : s ^ n = 0 ∨ t ^ n = 0) : f = g := by
  exact (expansion s t b f hf n hn).trans (expansion s t b g hg n hn).symm

/-- The two-step right-nilpotent case retains both ordered terms. -/
example (s : End X) (t : End Y) (b f : X ⟶ Y)
    (h : f = b + s ≫ f ≫ t) (ht : t ^ 2 = 0) :
    f = b + s ≫ b ≫ t := by
  simpa [Finset.sum_range_succ] using expansion s t b f h 2 (Or.inr ht)

/-- The left-nilpotent case is covered without reversing the composites. -/
example (s : End X) (t : End Y) (b f : X ⟶ Y)
    (h : f = b + s ≫ f ≫ t) (hs : s ^ 2 = 0) :
    f = b + s ≫ b ≫ t := by
  simpa [Finset.sum_range_succ] using expansion s t b f h 2 (Or.inl hs)

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private abbrev MatrixObject := SingleObj.star Mat
private def nilDot : Mat := !![0, 1; 0, 0]
private def coefficient : Mat := !![1, 2; 3, 4]
private def solution : Mat := coefficient + nilDot * coefficient
private def series : Mat := ∑ j ∈ Finset.range 2, nilDot ^ j * coefficient

private theorem nilDot_square : nilDot ^ 2 = 0 := by decide
private theorem solution_recurrence : solution = coefficient + nilDot * solution := by decide
private theorem series_recurrence : series = coefficient + nilDot * series := by decide

/-- A noncommutative integral fixture detects an exchange of ordered factors. -/
example : coefficient * nilDot ≠ nilDot * coefficient := by decide

example : solution = series + nilDot ^ 2 * solution := by
  have he := expansion_with_tail (C := SingleObj Mat) (X := MatrixObject) (Y := MatrixObject)
    1 (SingleObj.toEnd Mat nilDot) coefficient solution
    (by change solution = coefficient + nilDot * solution * 1
        simpa using solution_recurrence) 2
  change solution = (∑ j ∈ Finset.range 2, nilDot ^ j * coefficient * 1 ^ j) +
    nilDot ^ 2 * solution * 1 ^ 2 at he
  simpa [series] using he

example : solution = series := by
  have he := expansion (C := SingleObj Mat) (X := MatrixObject) (Y := MatrixObject)
    1 (SingleObj.toEnd Mat nilDot) coefficient solution
    (by change solution = coefficient + nilDot * solution * 1
        simpa using solution_recurrence) 2 (Or.inr nilDot_square)
  change solution = ∑ j ∈ Finset.range 2, nilDot ^ j * coefficient * 1 ^ j at he
  simpa [series] using he

example : solution = series := by
  exact unique (C := SingleObj Mat) (X := MatrixObject) (Y := MatrixObject)
    1 (SingleObj.toEnd Mat nilDot) coefficient solution series
    (by change solution = coefficient + nilDot * solution * 1
        simpa using solution_recurrence)
    (by change series = coefficient + nilDot * series * 1
        simpa using series_recurrence) 2 (Or.inr nilDot_square)

#print axioms expansion_with_tail
#print axioms expansion
#print axioms unique

end NonVacuity.MixedMateRecurrence

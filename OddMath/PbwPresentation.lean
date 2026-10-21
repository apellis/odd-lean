import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The presented ring of odd polynomials

Ellis-Khovanov-Lauda, arXiv:1111.1320v1, §2.1.1, (2.1) and (2.9): the ring of odd
polynomials is `ℤ⟨x_1, ..., x_n⟩ / (x_i x_j + x_j x_i = 0 for i ≠ j)`. This module builds
the presented ring `Presented n` with quotient generators `q i`.

The relation ideal is `TwoSidedIdeal.span` of the anticommutator words in
`FreeAlgebra ℤ (Fin n)`, viewed as an `Ideal` via `TwoSidedIdeal.asIdeal` so that
`Ideal.Quotient` applies. The two-sided span (rather than the one-sided `Ideal.span`) makes
the quotient a `Ring`; the instance comes from `TwoSidedIdeal.asIdeal.IsTwoSided`.

Main results:
- `rel_word_mem`: each anticommutator word lies in the relation ideal.
- `rel_sum` / `rel_anticommute`: `q_i * q_j + q_j * q_i = 0` and
  `q_i * q_j = -(q_j * q_i)` for `i ≠ j`.
- `mk_rel_zero`: the quotient map sends each relation word to `0`.
- `ideal_is_span` / `span_generates`: the relation ideal is the two-sided span of exactly
  the anticommutator words.
- `pair_mem_iff`: `(i,j) ∈ relPairs n ↔ i ≠ j`; in particular no diagonal pair `(i,i)` is
  imposed. That generator squares are actually nonzero in `Presented n` follows from the
  comparison with the model (`OddMath.PbwFactorization.Phi_sq_ne_zero`).
- `presentation_correct`: the conjunction of the relations and the generation statement.
-/

namespace OddMath.PbwPresentation

/-- Relation words: the anticommutator `ι i * ι j + ι j * ι i` for `i ≠ j`.
Word evaluation in `OddMath.PbwFactorization` kills these words. -/
def relSet (n : ℕ) : Set (FreeAlgebra ℤ (Fin n)) :=
  { w | ∃ i j : Fin n, i ≠ j ∧
    w = FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
      + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i }

/-- Relation indices: the off-diagonal pairs. The diagonal `(i,i)` is
excluded: no square-zero law is imposed. -/
def relPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

/-- Relation ideal, two-sided: the span of exactly the relation words. -/
def relTwoSided (n : ℕ) : TwoSidedIdeal (FreeAlgebra ℤ (Fin n)) :=
  TwoSidedIdeal.span (relSet n)

/-- Relation ideal as an `Ideal`, for the `Ideal.Quotient` API. -/
def relIdeal (n : ℕ) : Ideal (FreeAlgebra ℤ (Fin n)) :=
  TwoSidedIdeal.asIdeal (relTwoSided n)

instance relIdealTwoSided (n : ℕ) : (relIdeal n).IsTwoSided :=
  inferInstanceAs ((relTwoSided n).asIdeal.IsTwoSided)

/-- Presented object `P n`: the free algebra modulo the relation ideal. -/
def Presented (n : ℕ) : Type :=
  FreeAlgebra ℤ (Fin n) ⧸ relIdeal n

instance presentedRing (n : ℕ) : Ring (Presented n) :=
  Ideal.Quotient.ring (relIdeal n)

/-- Quotient generators `q_i`: the images of the free generators. -/
def q (n : ℕ) (i : Fin n) : Presented n :=
  Ideal.Quotient.mk (relIdeal n) (FreeAlgebra.ι ℤ i)

/-- Each anticommutator word lies in the relation ideal (it is one of
the spanning generators). -/
theorem rel_word_mem (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
      + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i ∈ relIdeal n := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span ⟨i, j, h, rfl⟩

/-- The imposed relations hold in the presented object — by
construction, the quotient map kills each spanning generator. -/
theorem rel_sum (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    q n i * q n j + q n j * q n i = 0 := by
  have h0 : Ideal.Quotient.mk (relIdeal n)
      (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
        + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (rel_word_mem n i j h)
  have e : q n i * q n j + q n j * q n i
      = Ideal.Quotient.mk (relIdeal n)
        (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
          + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) := by
    unfold q
    simp only [map_add, map_mul]
  rw [e]; exact h0

/-- Anticommute form of the imposed relations. -/
theorem rel_anticommute (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    q n i * q n j = -(q n j * q n i) :=
  add_eq_zero_iff_eq_neg.mp (rel_sum n i j h)

/-- The quotient map sends each relation word to `0`. -/
theorem mk_rel_zero (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Ideal.Quotient.mk (relIdeal n)
      (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j
        + FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (rel_word_mem n i j h)

/-- The relation ideal is the two-sided span of the relation words
(generation, definitional direction). -/
theorem ideal_is_span (n : ℕ) :
    relIdeal n
      = TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (relSet n)) :=
  rfl

/-- Every generating word lies in the relation ideal (generation,
membership direction). -/
theorem span_generates (n : ℕ) (w : FreeAlgebra ℤ (Fin n))
    (hw : w ∈ relSet n) : w ∈ relIdeal n := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span hw

/-- Index-level characterization — `(i,j)` is a relation index iff
`i ≠ j`. In particular the diagonal is never imposed. -/
theorem pair_mem_iff (n : ℕ) (i j : Fin n) :
    (i, j) ∈ relPairs n ↔ i ≠ j := by
  simp [relPairs]

/-- Adequacy conjunction: the relations hold in the presented object and
the relation ideal is generated by exactly these words. -/
theorem presentation_correct (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (q n i * q n j + q n j * q n i = 0)
    ∧ relIdeal n
      = TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (relSet n)) :=
  ⟨rel_sum n i j h, rfl⟩

end OddMath.PbwPresentation

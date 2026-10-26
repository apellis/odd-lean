import OddMath.SKM.RouquierSchur
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Nilpotence of feedback in a two-sided ideal filtration

This replaces the commutative determinant-nilradical step of
`Categorification/TwoRep/RouqCoproduct.lean` by an associative argument.
Its downstream consumer is separated-factor Rouquier inversion via
`RouquierSchur.isUnit_of_nilpotent_feedback`.

A multiplicative filtration of two-sided ideals controls every entry of
powers of the whole feedback matrix. No inference from entrywise nilpotence
alone is made. The categorical negative-window and dot-conjugation comparisons
must still put the feedback in such a filtration; they are not proved here.
-/
noncomputable section
namespace OddMath.SKM.RouquierSchur
open Matrix

variable {R : Type*} [Ring R]

/-- A coefficient-ideal filtration with the multiplication law needed for
matrix powers. The vanishing level is specified separately. -/
structure FeedbackIdealFiltration (R : Type*) [Ring R] where
  level : ℕ → TwoSidedIdeal R
  zero_eq_top : level 0 = ⊤
  mul_mem : ∀ {a b : ℕ} {x y : R}, x ∈ level a → y ∈ level b → x * y ∈ level (a + b)

namespace FeedbackIdealFiltration
variable (J : FeedbackIdealFiltration R)

/-- Arbitrary coefficients on the left preserve entrywise ideal membership. -/
theorem matrix_mul_mem_left {m n l : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n l R) (d : ℕ)
    (hB : ∀ i j, B i j ∈ J.level d) : ∀ i j, (A * B) i j ∈ J.level d := by
  intro i j
  apply TwoSidedIdeal.finsetSum_mem
  intro a _
  exact (J.level d).mul_mem_left _ _ (hB a j)

/-- Arbitrary coefficients on the right preserve entrywise ideal membership. -/
theorem matrix_mul_mem_right {m n l : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n l R) (d : ℕ)
    (hA : ∀ i j, A i j ∈ J.level d) : ∀ i j, (A * B) i j ∈ J.level d := by
  intro i j
  apply TwoSidedIdeal.finsetSum_mem
  intro a _
  exact (J.level d).mul_mem_right _ _ (hA i a)

/-- The nth power lies in level n as a whole matrix, including all sums
of ordered products. This is stronger than entrywise nilpotence. -/
theorem matrix_pow_mem {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n R) (hN : ∀ i j, N i j ∈ J.level 1) (d : ℕ) :
    ∀ i j, (N ^ d) i j ∈ J.level d := by
  induction d with
  | zero => simp [J.zero_eq_top]
  | succ d ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    apply TwoSidedIdeal.finsetSum_mem
    intro a _
    exact J.mul_mem (ih i a) (hN a j)

/-- A vanishing ideal level kills the entire feedback operator. -/
theorem matrix_isNilpotent {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n R) (hN : ∀ i j, N i j ∈ J.level 1)
    (d : ℕ) (hd : J.level d = ⊥) : IsNilpotent N := by
  refine ⟨d, ?_⟩
  ext i j
  have h := J.matrix_pow_mem N hN d i j
  simpa [hd] using h

/-- An off-diagonal block in level one puts the full feedback there, despite
the arbitrary pivot inverses and the other off-diagonal block. -/
theorem feedback_mem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : (Matrix m m R)ˣ) (D : (Matrix n n R)ˣ)
    (B : Matrix m n R) (C : Matrix n m R)
    (hC : ∀ i j, C i j ∈ J.level 1) :
    ∀ i j, ((↑(D⁻¹) : Matrix n n R) * C * (↑(A⁻¹) : Matrix m m R) * B) i j ∈ J.level 1 := by
  apply J.matrix_mul_mem_right
  apply J.matrix_mul_mem_right
  exact J.matrix_mul_mem_left _ _ 1 hC

/-- Whole-feedback membership in a vanishing two-sided ideal filtration
suffices, even when neither off-diagonal block lies there separately. -/
theorem isUnit_of_feedback_filtration {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : (Matrix m m R)ˣ) (D : (Matrix n n R)ˣ)
    (B : Matrix m n R) (C : Matrix n m R)
    (hN : ∀ i j,
      ((↑(D⁻¹) : Matrix n n R) * C * (↑(A⁻¹) : Matrix m m R) * B) i j ∈ J.level 1)
    (d : ℕ) (hd : J.level d = ⊥) : IsUnit (fromBlocks (↑A) B C (↑D)) :=
  isUnit_of_nilpotent_feedback A D B C (J.matrix_isNilpotent _ hN d hd)

/-- Associative block inversion from a nilpotent coefficient ideal filtration.
The coupled inverse is a conclusion, not an input. -/
theorem isUnit_of_ideal_feedback {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : (Matrix m m R)ˣ) (D : (Matrix n n R)ˣ)
    (B : Matrix m n R) (C : Matrix n m R)
    (hC : ∀ i j, C i j ∈ J.level 1) (d : ℕ) (hd : J.level d = ⊥) :
    IsUnit (fromBlocks (↑A) B C (↑D)) :=
  isUnit_of_nilpotent_feedback A D B C
    (J.matrix_isNilpotent _ (J.feedback_mem A D B C hC) d hd)

end FeedbackIdealFiltration
end OddMath.SKM.RouquierSchur

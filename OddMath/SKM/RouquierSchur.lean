import Mathlib.Data.Matrix.Block
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Associative Schur lifting for parity-shifted blocks

Ports the algebraic lifting step of `Categorification/TwoRep/RouqCoproduct.lean`
(`isIso_lift_of_schur`) and `Categorification/TwoRep/RouqCoproductNeg.lean`.
Unlike the commutative determinant argument, the coefficient ring here is
only associative. The hypothesis is nilpotence of the whole feedback
operator, not nilpotence of its entries. In a super application these
matrices must first be coordinates of even maps between the specified
parity-shifted summands. The theorem does not assert that the actual fused
Rouquier map has these coordinates or that its feedback is nilpotent.
-/
noncomputable section
namespace OddMath.SKM.RouquierSchur
open Matrix
variable {R m n : Type*} [Ring R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The upper shear and its inverse require no commutativity. -/
def upper (B : Matrix m n R) : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ where
  val := fromBlocks 1 B 0 1
  inv := fromBlocks 1 (-B) 0 1
  val_inv := by simp [fromBlocks_multiply, fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, fromBlocks_one]

/-- The lower shear and its inverse require no commutativity. -/
def lower (C : Matrix n m R) : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ where
  val := fromBlocks 1 0 C 1
  inv := fromBlocks 1 0 (-C) 1
  val_inv := by simp [fromBlocks_multiply, fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, fromBlocks_one]

/-- Block diagonal units over an arbitrary associative coefficient ring. -/
def diagonal (A : (Matrix m m R)ˣ) (D : (Matrix n n R)ˣ) :
    (Matrix (m ⊕ n) (m ⊕ n) R)ˣ where
  val := fromBlocks A 0 0 D
  inv := fromBlocks (↑(A⁻¹) : Matrix m m R) 0 0 (↑(D⁻¹) : Matrix n n R)
  val_inv := by simp [fromBlocks_multiply, fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, fromBlocks_one]

/-- LDU factorization with a prescribed inverse of the first pivot. -/
theorem factor (A : (Matrix m m R)ˣ) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) :
    fromBlocks (↑A) B C D =
      (lower (C * (↑(A⁻¹) : Matrix m m R))).val * fromBlocks (↑A) 0 0 (D - C * (↑(A⁻¹) : Matrix m m R) * B) *
        (upper ((↑(A⁻¹) : Matrix m m R) * B)).val := by
  simp [lower, upper, fromBlocks_multiply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]
  simp

/-- The Schur-complement criterion, without a commutative determinant. -/
theorem isUnit_of_schur (A : (Matrix m m R)ˣ) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) (hS : IsUnit (D - C * (↑(A⁻¹) : Matrix m m R) * B)) :
    IsUnit (fromBlocks (↑A) B C D) := by
  obtain ⟨S, hS⟩ := hS
  rw [factor A B C D, ← hS]
  exact ((lower (C * (↑(A⁻¹) : Matrix m m R))).isUnit.mul (diagonal A S).isUnit).mul
    (upper ((↑(A⁻¹) : Matrix m m R) * B)).isUnit

/-- Nilpotent feedback proves the Schur complement invertible; it is not
assumed as a field of the resulting coupled action. -/
theorem isUnit_of_nilpotent_feedback (A : (Matrix m m R)ˣ) (D : (Matrix n n R)ˣ)
    (B : Matrix m n R) (C : Matrix n m R)
    (hN : IsNilpotent ((↑(D⁻¹) : Matrix n n R) * C * (↑(A⁻¹) : Matrix m m R) * B)) :
    IsUnit (fromBlocks (↑A) B C (↑D)) := by
  apply isUnit_of_schur
  have hS : (↑D : Matrix n n R) - C * (↑(A⁻¹) : Matrix m m R) * B =
      (↑D : Matrix n n R) * (1 - (↑(D⁻¹) : Matrix n n R) * C * (↑(A⁻¹) : Matrix m m R) * B) := by
    simp [mul_sub, Matrix.mul_assoc]
  rw [hS]
  exact D.isUnit.mul hN.isUnit_one_sub

end OddMath.SKM.RouquierSchur

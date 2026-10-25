import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Signed right multipliers and the mixed quadratic sign

For odd `u`, signed right multiplication on a regular supermodule is
`h ↦ σ(h) * u`, where `σ` is the parity involution. Its square is minus
right multiplication by `u²`. In particular, negating both crossings does
not repair a mixed odd/odd quadratic relation with nonzero constant term.

The rational four-dimensional example is the regular module of two-by-two
matrices, with even diagonal word idempotents and odd off-diagonal crossings.
Taking both dots zero gives the two-distinct-colour, zero-edge, cutoff-one
quadratic block. It isolates the mixed quadratic sign; it is not an action
of the entire quiver Hecke category. No projectivity or
cyclotomic action is asserted here.
-/
namespace OddMath.QuiverHecke.CyclotomicAction

variable {A : Type*} [Ring A]

/-- Signed right multiplication by an odd homogeneous element. -/
def oddRight (σ : A →+* A) (u h : A) : A := σ h * u

/-- The super-opposite sign for two odd right multipliers, including their order. -/
theorem oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    oddRight σ u (oddRight σ v h) = -(h * (v * u)) := by
  simp only [oddRight, map_mul, hσ h, hv, mul_neg, neg_mul, mul_assoc]

/-- A simultaneous minus on both odd crossings leaves the quadratic sign unchanged. -/
theorem neg_oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    -oddRight σ u (-oddRight σ v h) = -(h * (v * u)) := by
  simpa only [oddRight, map_neg, neg_mul, neg_neg] using oddRight_comp σ hσ u v hv h

/-- Opposite signs on the two directed odd crossings repair the constant square. -/
theorem asymmetric_oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    -oddRight σ u (oddRight σ v h) = h * (v * u) := by
  rw [oddRight_comp σ hσ u v hv, neg_neg]

/-- The two word idempotents are the diagonal matrix units. -/
abbrev TwoWordAlgebra := Matrix (Fin 2) (Fin 2) ℚ

def parityMatrix : TwoWordAlgebra := !![1, 0; 0, -1]

theorem parityMatrix_square : parityMatrix * parityMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [parityMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Parity fixes the word idempotents and negates the directed crossings. -/
def matrixParity : TwoWordAlgebra →+* TwoWordAlgebra where
  toFun h := parityMatrix * h * parityMatrix
  map_one' := by simpa using parityMatrix_square
  map_mul' a b := by
    change parityMatrix * (a * b) * parityMatrix =
      (parityMatrix * a * parityMatrix) * (parityMatrix * b * parityMatrix)
    calc
      _ = parityMatrix * a * (parityMatrix * parityMatrix) * b * parityMatrix := by
        rw [parityMatrix_square]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]

/-- Sum of the two directed crossings in the disconnected odd/odd example. -/
def oddUnit : TwoWordAlgebra := !![0, 1; 1, 0]

theorem matrixParity_involutive : Function.Involutive matrixParity := by
  intro h
  change parityMatrix * (parityMatrix * h * parityMatrix) * parityMatrix = h
  calc
    _ = (parityMatrix * parityMatrix) * h * (parityMatrix * parityMatrix) := by
      simp only [mul_assoc]
    _ = h := by rw [parityMatrix_square]; simp

theorem oddUnit_parity : matrixParity oddUnit = -oddUnit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixParity, parityMatrix, oddUnit, Matrix.mul_apply, Fin.sum_univ_two]

theorem oddUnit_square : oddUnit * oddUnit = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [oddUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact regular-module failure of an unchanged constant quadratic relation. -/
theorem uniform_crossing_sign_fails :
    -oddRight matrixParity oddUnit (-oddRight matrixParity oddUnit (1 : TwoWordAlgebra)) ≠ 1 := by
  rw [neg_oddRight_comp matrixParity matrixParity_involutive oddUnit oddUnit oddUnit_parity,
    oddUnit_square, mul_one]
  intro h
  have := congrArg (fun m : TwoWordAlgebra => m 0 0) h
  norm_num at this

/-- Negating only one multiplier repairs the composition in this test. -/
theorem directed_crossing_sign_passes :
    -oddRight matrixParity oddUnit (oddRight matrixParity oddUnit (1 : TwoWordAlgebra)) = 1 := by
  rw [asymmetric_oddRight_comp matrixParity matrixParity_involutive oddUnit oddUnit oddUnit_parity,
    oddUnit_square, mul_one]

end OddMath.QuiverHecke.CyclotomicAction

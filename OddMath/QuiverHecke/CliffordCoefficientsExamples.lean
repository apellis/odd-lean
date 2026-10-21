/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordCoefficients

/-! # Nonzero polynomial–Clifford coefficient operators -/

noncomputable section
namespace OddMath.QuiverHecke.CliffordCoefficients.Examples

/-- The constant coefficient used to test the operators. -/
def vacuum : Coeff ℚ 2 := monomial 0 1

/-- The ordinary variable square does not vanish on the constant coefficient. -/
theorem Y_sq_vacuum (i : Fin 2) :
    (Y (R := ℚ) i ^ 2) vacuum =
      monomial (SkewPolynomial.expSingle i + SkewPolynomial.expSingle i) 1 := by
  simp [vacuum, pow_two, Module.End.mul_apply]

/-- The odd square is nonzero, and has the negative ordinary square. -/
theorem X_sq_ne_zero (i : Fin 2) : X (R := ℚ) (fun _ => true) i ^ 2 ≠ 0 := by
  intro h
  have heq := X_sq_odd (R := ℚ) (fun _ : Fin 2 => true) i rfl
  rw [h] at heq
  have hz : Y (R := ℚ) i ^ 2 = 0 := by
    apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun heq.symm v
    change -((Y (R := ℚ) i ^ 2) v) = 0 at hv
    exact neg_eq_zero.mp hv
  have hv := congrArg (fun f : Module.End ℚ (Coeff ℚ 2) => f vacuum) hz
  rw [Y_sq_vacuum] at hv
  have hc := congrArg (fun f : Coeff ℚ 2 =>
    f (SkewPolynomial.expSingle i + SkewPolynomial.expSingle i)) hv
  simp [monomial] at hc

/-- Distinct odd dot operators have the required sign. -/
example : X (R := ℚ) (fun _ : Fin 2 => true) 0 * X (fun _ => true) 1 =
    -(X (fun _ => true) 1 * X (fun _ => true) 0) := by
  have h := X_supercommute (R := ℚ) (fun _ : Fin 2 => true) 0 1 (by decide)
  apply h.trans
  apply LinearMap.ext
  intro v
  rfl

/-- The mixed-parity case has no spurious minus sign. -/
example : X (R := ℚ) (fun i : Fin 2 => i == 0) 0 * X (fun i => i == 0) 1 =
    X (fun i => i == 0) 1 * X (fun i => i == 0) 0 := by
  simpa using X_supercommute (R := ℚ) (fun i : Fin 2 => i == 0) 0 1 (by decide)

/-- The coefficient relations themselves also hold in characteristic two. -/
example (i : Fin 2) : C (R := ZMod 2) i * C i = 1 := C_sq i

#print axioms C_sq
#print axioms C_anticommute
#print axioms C_Y_self
#print axioms C_Y_of_ne
#print axioms X_supercommute
#print axioms X_sq_odd
#print axioms X_sq_ne_zero

end OddMath.QuiverHecke.CliffordCoefficients.Examples

import OddMath.LrShapeCensus
import OddMath.LrSignDiagonal
import OddMath.LrCoeffMatrix

/-!
# Diagonal matrices of sign diagonals

The unit diagonals of `OddMath.LrSignDiagonal` as diagonal matrices
(`OddMath.LrCoeffMatrix.coeffDiag`) over the census of `OddMath.LrShapeCensus`.

Main results:
- `unitLead_one` / `unitLead_negOne` / `unitLead_sign`: the constant diagonals and the
  diagonal of any sign assignment are unit diagonals.
- `coeffUnitOne_self` / `coeffUnitOne_offdiag`: the matrix of the all-ones diagonal has `1`
  on and `0` off the diagonal; likewise `coeffUnitNegOne_*` with `-1` and `coeffUnitSign_*`
  with `signOf (s i)`.
- `coeffUnitOne_ne_zero` / `coeffUnitNegOne_ne_zero`: these matrices are not the zero matrix.
- `coeffUnitOne_eq_sign` / `coeffUnitNegOne_eq_sign`: the matrices of the constant diagonals
  agree entrywise with those of the constant sign assignments.
-/

namespace OddMath.LrSignDiagonalMatrix

open OddMath.LrShapeCensus
open OddMath.LrSignDiagonal
open OddMath.LrCoeffMatrix

/-- The all-ones diagonal is a unit diagonal (`diagOne_isUnit`). -/
theorem unitLead_one (wt : Nat) : IsUnitDiag wt (diagOne wt) :=
  diagOne_isUnit wt

/-- The all-minus-ones diagonal is a unit diagonal (`diagNegOne_isUnit`). -/
theorem unitLead_negOne (wt : Nat) : IsUnitDiag wt (diagNegOne wt) :=
  diagNegOne_isUnit wt

/-- The diagonal of any sign assignment is a unit diagonal (`diagSign_isUnit`). -/
theorem unitLead_sign (wt : Nat) (s : Fin (shapeCount wt) → Bool) :
    IsUnitDiag wt (diagSign wt s) :=
  diagSign_isUnit wt s

/-- The diagonal matrix of `diagOne` has `1` on the diagonal (`coeffDiag_self` composed with
    the `diagOne` computation rule). -/
theorem coeffUnitOne_self (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagOne wt) i i = 1 := by
  rw [coeffDiag_self wt (diagOne wt) i]
  rfl

/-- The diagonal matrix of `diagOne` vanishes off the diagonal. -/
theorem coeffUnitOne_offdiag (wt : Nat) (i j : Fin (shapeCount wt))
    (h : i ≠ j) :
    coeffDiag wt (diagOne wt) i j = 0 :=
  coeffDiag_offdiag wt (diagOne wt) i j h

/-- The diagonal matrix of `diagNegOne` has `-1` on the diagonal. -/
theorem coeffUnitNegOne_self (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagNegOne wt) i i = -1 := by
  rw [coeffDiag_self wt (diagNegOne wt) i]
  rfl

/-- The diagonal matrix of `diagNegOne` vanishes off the diagonal. -/
theorem coeffUnitNegOne_offdiag (wt : Nat) (i j : Fin (shapeCount wt))
    (h : i ≠ j) :
    coeffDiag wt (diagNegOne wt) i j = 0 :=
  coeffDiag_offdiag wt (diagNegOne wt) i j h

/-- The diagonal matrix of `diagSign wt s` has `signOf (s i)` on the
    diagonal (`coeffDiag_self` composed with the `diagSign` computation
    rule). -/
theorem coeffUnitSign_self (wt : Nat) (s : Fin (shapeCount wt) → Bool)
    (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagSign wt s) i i = signOf (s i) := by
  rw [coeffDiag_self wt (diagSign wt s) i]
  rfl

/-- The diagonal matrix of a sign diagonal vanishes off the diagonal. -/
theorem coeffUnitSign_offdiag (wt : Nat) (s : Fin (shapeCount wt) → Bool)
    (i j : Fin (shapeCount wt)) (h : i ≠ j) :
    coeffDiag wt (diagSign wt s) i j = 0 :=
  coeffDiag_offdiag wt (diagSign wt s) i j h

/-- The diagonal matrix of `diagOne` is not the zero matrix; `diagOne wt` is
    definitionally `fun _ => 1`, so this is `coeffDiag_one_ne_zero`. -/
theorem coeffUnitOne_ne_zero (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagOne wt) ≠ coeffZero wt :=
  coeffDiag_one_ne_zero wt i

/-- The diagonal matrix of `diagNegOne` is not the zero matrix (`congrFun` and
    `-1 ≠ 0`). -/
theorem coeffUnitNegOne_ne_zero (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagNegOne wt) ≠ coeffZero wt := by
  intro heq
  have hc : coeffDiag wt (diagNegOne wt) i i = coeffZero wt i i :=
    congrFun (congrFun heq i) i
  rw [coeffDiag_self, coeffZero_apply] at hc
  have hneg : diagNegOne wt i = -1 := rfl
  rw [hneg] at hc
  exact (by decide : (-1 : Int) ≠ 0) hc

/-- The diagonal matrix of `diagOne` agrees entrywise with that of the constant-`true`
    sign assignment. -/
theorem coeffUnitOne_eq_sign (wt : Nat) (i j : Fin (shapeCount wt)) :
    coeffDiag wt (diagOne wt) i j =
      coeffDiag wt (diagSign wt (fun _ => true)) i j := by
  unfold coeffDiag
  rw [diagOne_eq_sign_apply wt i]

/-- The diagonal matrix of `diagNegOne` agrees entrywise with that of the
    constant-`false` sign assignment. -/
theorem coeffUnitNegOne_eq_sign (wt : Nat) (i j : Fin (shapeCount wt)) :
    coeffDiag wt (diagNegOne wt) i j =
      coeffDiag wt (diagSign wt (fun _ => false)) i j := by
  unfold coeffDiag
  rw [diagNegOne_eq_sign_apply wt i]

set_option maxRecDepth 10000

/- Evaluated values. Index `0` uses `idx0_lt`; the second index uses `decide` on
   `shapeCount 4 = 5`. The increased recursion limit supports reduction of the census. -/
#eval ("u1", diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("un", diagNegOne 4 ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("cu11", coeffDiag 4 (diagOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("cu10", coeffDiag 4 (diagOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨1, by decide⟩)
#eval ("cun11", coeffDiag 4 (diagNegOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("dz", coeffDiag 4 (diagOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩ != coeffZero 4 ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("sg", decide (diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩ = diagSign 4 (fun _ => true) ⟨0, idx0_lt 4 (by decide)⟩))
#eval ("cnt4", shapeCount 4)

/- Axiom checks. -/
#print axioms unitLead_one
#print axioms unitLead_negOne
#print axioms unitLead_sign
#print axioms coeffUnitOne_self
#print axioms coeffUnitOne_offdiag
#print axioms coeffUnitNegOne_self
#print axioms coeffUnitNegOne_offdiag
#print axioms coeffUnitSign_self
#print axioms coeffUnitSign_offdiag
#print axioms coeffUnitOne_ne_zero
#print axioms coeffUnitNegOne_ne_zero
#print axioms coeffUnitOne_eq_sign
#print axioms coeffUnitNegOne_eq_sign

end OddMath.LrSignDiagonalMatrix

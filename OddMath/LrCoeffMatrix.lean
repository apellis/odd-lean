import OddMath.LrShapeCensus

/-!
# Coefficient matrices and right-hand sides indexed by the census

`CoeffMat wt` is the type of `Int` matrices and `RhsVec wt M` the type of `M`-valued
vectors indexed by the partitions of `wt` (`OddMath.LrShapeCensus`): the shape of the
coefficient matrix and right-hand side of a census-indexed unitriangular system
(`OddMath.LrTriangular.RowSystem`). No coefficients of a Pieri rule are defined here.

Main results (Lean core only, besides `OddMath.LrShapeCensus`):
- `coeffZero` / `rhsZero`: the zero matrix and vector, with `coeffZero_apply`, `rhsZero_apply`.
- `coeffDiag d`: the diagonal matrix with diagonal `d`.
- `coeffDiag_self` / `coeffDiag_offdiag`: its diagonal and off-diagonal entries.
- `coeffDiag_one_ne_zero`: the identity diagonal matrix is not the zero matrix.
-/

namespace OddMath.LrCoeffMatrix

open OddMath.LrShapeCensus

/-- Square `Int` matrices indexed by the partitions of `wt`. -/
abbrev CoeffMat (wt : Nat) : Type := Fin (shapeCount wt) → Fin (shapeCount wt) → Int

/-- Vectors with values in `M` indexed by the partitions of `wt`. -/
abbrev RhsVec (wt : Nat) (M : Type) : Type := Fin (shapeCount wt) → M

/-- The zero coefficient matrix. -/
def coeffZero (wt : Nat) : CoeffMat wt := fun _ _ => 0

/-- The zero right-hand-side vector over `Int`. -/
def rhsZero (wt : Nat) : RhsVec wt Int := fun _ => 0

/-- The diagonal matrix with diagonal `d`. -/
def coeffDiag (wt : Nat) (d : Fin (shapeCount wt) → Int) : CoeffMat wt :=
  fun i j => if i = j then d i else 0

/-- Computation rule for the zero matrix. -/
theorem coeffZero_apply (wt : Nat) (i j : Fin (shapeCount wt)) :
    coeffZero wt i j = 0 := by
  rfl

/-- Computation rule for the zero vector. -/
theorem rhsZero_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    rhsZero wt i = 0 := by
  rfl

/-- Diagonal projection: a diagonal matrix reads off its lead assignment
    on the diagonal. -/
theorem coeffDiag_self (wt : Nat) (d : Fin (shapeCount wt) → Int)
    (i : Fin (shapeCount wt)) :
    coeffDiag wt d i i = d i := by
  simp [coeffDiag]

/-- Off-diagonal vanishing: a diagonal matrix is zero away from the
    diagonal. -/
theorem coeffDiag_offdiag (wt : Nat) (d : Fin (shapeCount wt) → Int)
    (i j : Fin (shapeCount wt)) (h : i ≠ j) :
    coeffDiag wt d i j = 0 := by
  simp [coeffDiag, h]

/-- The identity diagonal matrix is not the zero matrix (`congrFun` at a given index). -/
theorem coeffDiag_one_ne_zero (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (fun _ => 1) ≠ coeffZero wt := by
  intro heq
  have hc : coeffDiag wt (fun _ => 1) i i = coeffZero wt i i :=
    congrFun (congrFun heq i) i
  rw [coeffDiag_self, coeffZero_apply] at hc
  exact (by decide : (1 : Int) ≠ 0) hc

set_option maxRecDepth 10000

/- Evaluated values. Index-validity proofs use `decide` on `shapeCount 4 = 5`; the
   increased recursion limit supports reduction of the census. -/
#eval ("cz00", coeffZero 4 ⟨0, by decide⟩ ⟨0, by decide⟩)
#eval ("rz0", rhsZero 4 ⟨0, by decide⟩)
#eval ("dg11", coeffDiag 4 (fun _ => 1) ⟨0, by decide⟩ ⟨0, by decide⟩)
#eval ("dg10", coeffDiag 4 (fun _ => 1) ⟨0, by decide⟩ ⟨1, by decide⟩)
#eval ("dz", coeffDiag 4 (fun _ => 1) ⟨0, by decide⟩ ⟨0, by decide⟩ != coeffZero 4 ⟨0, by decide⟩ ⟨0, by decide⟩)
#eval ("cnt4", shapeCount 4)

/- Axiom checks. -/
#print axioms coeffZero_apply
#print axioms rhsZero_apply
#print axioms coeffDiag_self
#print axioms coeffDiag_offdiag
#print axioms coeffDiag_one_ne_zero

end OddMath.LrCoeffMatrix

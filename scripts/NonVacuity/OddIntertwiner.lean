import OddMath.Diagrams.OddNilHecke.Intertwiner
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Importing tests with a nonzero integral matrix intertwiner. -/

namespace NonVacuity.OddIntertwiner

open OddMath.OddNilHecke.Intertwiner

private def X : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 1]
private def Y : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 1, 0]
private def T : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

private theorem relations :
    T * T = 0 ∧ X * Y + Y * X = 0 ∧ T * X + Y * T = 1 ∧ X * T + T * Y = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [X, Y, T, Matrix.mul_apply, Fin.sum_univ_two]

example : element X Y T ^ 2 = -(squareDiff X Y ^ 2 * (X ^ 2 + Y ^ 2)) :=
  (identities X Y T relations.1 relations.2.1 relations.2.2.1 relations.2.2.2).1

example : element X Y T = !![-1, -1; 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [element, squareDiff, X, Y, T, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

example : element X Y T ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  norm_num [element, squareDiff, X, Y, T, pow_two, Matrix.mul_apply, Fin.sum_univ_two] at he

open OddMath.Diagrams.OddNilHecke in
example : intertwiner (ZMod 4) 3 1 * x (ZMod 4) 3 1 =
    -(x (ZMod 4) 3 2 * intertwiner (ZMod 4) 3 1) :=
  (intertwiner_dot_transport (ZMod 4) (n := 3) (i := 1) (by decide)).1

#print axioms OddMath.OddNilHecke.Intertwiner.identities
#print axioms OddMath.OddNilHecke.Intertwiner.anticommutes
#print axioms OddMath.Diagrams.OddNilHecke.intertwiner_square
#print axioms OddMath.Diagrams.OddNilHecke.intertwiner_dot_transport

end NonVacuity.OddIntertwiner

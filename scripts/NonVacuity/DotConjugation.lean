import OddMath.SKM.RouquierDotConjugation
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.LinearAlgebra.Matrix.Notation

/-! All-length conjugation on two noncommuting integral shear dots.
The cap–cup correction is retained and is nonzero for both signs. -/
noncomputable section
open CategoryTheory OddMath.SKM
open scoped BigOperators
namespace NonVacuity.DotConjugation
private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private abbrev Obj := SingleObj.star Mat
private def x : Mat := !![1, 1; 0, 1]
private def wx : Mat := !![1, -1; 0, 1]
private def y : Mat := !![1, 0; 1, 1]
private def wy : Mat := !![1, 0; -1, 1]
private def f : Mat := !![1, 2; 3, 4]
private def b (q : ℤ) : Mat := f * x - q • (y * f)

example : x * y ≠ y * x := by decide
example : b (-1) ≠ 0 := by decide
example : b 1 ≠ 0 := by decide

example (q : ℤ) (n : ℕ) :
    q ^ n • (((SingleObj.toEnd Mat wx) ^ n) ≫ f ≫ ((SingleObj.toEnd Mat y) ^ n)) =
      f - ∑ j ∈ Finset.range n, q ^ j •
        (((SingleObj.toEnd Mat wx) ^ (j + 1)) ≫ b q ≫ ((SingleObj.toEnd Mat y) ^ j)) := by
  exact mate_dot_conjugation_source (X := Obj) (Y := Obj)
    (SingleObj.toEnd Mat x) (SingleObj.toEnd Mat wx) (SingleObj.toEnd Mat y)
    (b q) f q rfl (by change x * wx = 1; decide) n

example (n : ℕ) :
    (-1 : ℤ) ^ n • (((SingleObj.toEnd Mat x) ^ n) ≫ f ≫ ((SingleObj.toEnd Mat wy) ^ n)) =
      f + ∑ j ∈ Finset.range n, (-1 : ℤ) ^ (j + 1) •
        (((SingleObj.toEnd Mat x) ^ j) ≫ b (-1) ≫ ((SingleObj.toEnd Mat wy) ^ (j + 1))) := by
  exact mate_dot_conjugation_target (X := Obj) (Y := Obj)
    (SingleObj.toEnd Mat x) (SingleObj.toEnd Mat y) (SingleObj.toEnd Mat wy)
    (b (-1)) f (-1) (by decide) rfl (by change wy * y = 1; decide) n

example (n : ℕ) :
    (1 : ℤ) ^ n • (((SingleObj.toEnd Mat x) ^ n) ≫ f ≫ ((SingleObj.toEnd Mat wy) ^ n)) =
      f + ∑ j ∈ Finset.range n, (1 : ℤ) ^ (j + 1) •
        (((SingleObj.toEnd Mat x) ^ j) ≫ b 1 ≫ ((SingleObj.toEnd Mat wy) ^ (j + 1))) := by
  exact mate_dot_conjugation_target (X := Obj) (Y := Obj)
    (SingleObj.toEnd Mat x) (SingleObj.toEnd Mat y) (SingleObj.toEnd Mat wy)
    (b 1) f 1 (by decide) rfl (by change wy * y = 1; decide) n

#print axioms mate_dot_conjugation_source
#print axioms mate_dot_conjugation_target
end NonVacuity.DotConjugation

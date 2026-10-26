import OddMath.SKM.RouquierMateSeries
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Noncommutative integral fixtures for both signs and both ordered series.
The reservoir dot has square zero, and the probe dot is the identity. -/
noncomputable section
open CategoryTheory OddMath.SKM
open scoped BigOperators
namespace NonVacuity.MateSeries
private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private abbrev Obj := SingleObj.star Mat
private def nilDot : Mat := !![0, 1; 0, 0]
private def coefficient : Mat := !![1, 2; 3, 4]
private def cSolution (q : ℤ) : Mat := coefficient + q • (nilDot * coefficient)
private def dSolution (q : ℤ) : Mat := -q • coefficient - coefficient * nilDot

example : coefficient * nilDot ≠ nilDot * coefficient := by decide

example : cSolution (-1) =
    ∑ j ∈ Finset.range 2, (-1 : ℤ) ^ j •
      (((1 : End Obj) ^ (j + 1)) ≫ coefficient ≫ ((SingleObj.toEnd Mat nilDot) ^ j)) := by
  exact mate_series_probe_source (X := Obj) (Y := Obj)
    1 1 (SingleObj.toEnd Mat nilDot) coefficient (cSolution (-1)) (-1)
    (by change cSolution (-1) * 1 - ((-1) : ℤ) • (nilDot * cSolution (-1)) = coefficient; decide)
    (by simp) 2 (by change nilDot ^ 2 = 0; decide)

example : cSolution 1 =
    ∑ j ∈ Finset.range 2, (1 : ℤ) ^ j •
      (((1 : End Obj) ^ (j + 1)) ≫ coefficient ≫ ((SingleObj.toEnd Mat nilDot) ^ j)) := by
  exact mate_series_probe_source (X := Obj) (Y := Obj)
    1 1 (SingleObj.toEnd Mat nilDot) coefficient (cSolution 1) 1
    (by change cSolution 1 * 1 - (1 : ℤ) • (nilDot * cSolution 1) = coefficient; decide)
    (by simp) 2 (by change nilDot ^ 2 = 0; decide)

example : dSolution (-1) =
    -(∑ j ∈ Finset.range 2, (-1 : ℤ) ^ (j + 1) •
      (((SingleObj.toEnd Mat nilDot) ^ j) ≫ coefficient ≫ ((1 : End Obj) ^ (j + 1)))) := by
  exact mate_series_probe_target (X := Obj) (Y := Obj)
    (SingleObj.toEnd Mat nilDot) 1 1 coefficient (dSolution (-1)) (-1)
    (by decide)
    (by change dSolution (-1) * nilDot - ((-1) : ℤ) • (1 * dSolution (-1)) = coefficient; decide)
    (by simp) 2 (by change nilDot ^ 2 = 0; decide)

example : dSolution 1 =
    -(∑ j ∈ Finset.range 2, (1 : ℤ) ^ (j + 1) •
      (((SingleObj.toEnd Mat nilDot) ^ j) ≫ coefficient ≫ ((1 : End Obj) ^ (j + 1)))) := by
  exact mate_series_probe_target (X := Obj) (Y := Obj)
    (SingleObj.toEnd Mat nilDot) 1 1 coefficient (dSolution 1) 1
    (by decide)
    (by change dSolution 1 * nilDot - (1 : ℤ) • (1 * dSolution 1) = coefficient; decide)
    (by simp) 2 (by change nilDot ^ 2 = 0; decide)

#print axioms mate_signed_series_with_tail
#print axioms mate_series_probe_source
#print axioms mate_series_probe_target
end NonVacuity.MateSeries

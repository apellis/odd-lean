import OddMath.SKM.RouquierMateSlide
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.LinearAlgebra.Matrix.Notation

/-! An occupied, noncommutative projection fixture for the signed dot slide.
It tests the ordered projection theorem, not a coupled categorical action. -/
noncomputable section
open CategoryTheory OddMath.SKM
namespace NonVacuity.MateSlide
private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private abbrev Obj := SingleObj.star Mat
private def x : Mat := !![0, 1; 0, 0]
private def y : Mat := !![1, 0; 0, 1]
private def f : Mat := !![1, 2; 3, 4]
private def b : Mat := f * x + y * f

example : x * f ≠ f * x := by decide

example : (SingleObj.toEnd Mat x) ≫ (𝟙 Obj ≫ f ≫ 𝟙 Obj) -
    (-1 : ℤ) • ((𝟙 Obj ≫ f ≫ 𝟙 Obj) ≫ SingleObj.toEnd Mat y) =
      𝟙 Obj ≫ b ≫ 𝟙 Obj := by
  exact mate_slide_projection f b (SingleObj.toEnd Mat x) (SingleObj.toEnd Mat y)
    (-1) (by change f * x - (-1 : ℤ) • (y * f) = b; simp [b])
    (𝟙 Obj) (𝟙 Obj) (SingleObj.toEnd Mat x) (SingleObj.toEnd Mat y)
    (by simp) (by simp)

#print axioms rouquierMate_normalized_slide
#print axioms mate_slide_projection
end NonVacuity.MateSlide

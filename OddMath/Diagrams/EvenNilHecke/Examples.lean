import OddMath.Diagrams.EvenNilHecke.Demazure
import Mathlib.Data.Matrix.Mul

/-!
# Integral consumers of the even nilHecke presentation

A two-strand matrix representation over the integers verifies that the
presentation and its two complementary Demazure idempotents are nonzero.
This is a consumer of the prerequisites to BE2 Lemma 11.1, not a factorial
splitting or a claim of faithfulness of this specialization.
-/

namespace OddMath.EvenNilHecke.Examples

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def x : Fin 2 → Mat := ![!![0, 0; 1, 0], !![0, 0; -1, 0]]
def t : Fin 1 → Mat := fun _ => !![0, 1; 0, 0]

/-- Specialize the two elementary symmetric polynomials to zero. -/
def matrixFamily : Family 0 Mat where
  x := x
  t := t
  square := by decide
  braid := by intro i j h; have hi := i.isLt; have hj := j.isLt; omega
  dots := by decide
  distant := by intro i j h; have hi := i.isLt; have hj := j.isLt; omega
  mixedRight := by decide
  mixedLeft := by decide
  spectator := by
    intro i j hl hr
    fin_cases i
    fin_cases j <;> simp_all

noncomputable def matrixMap : Presented 0 →+* Mat := matrixFamily.lift

@[simp] theorem matrixMap_demazure :
    matrixMap (demazure 0 0) = !![1, 0; 0, 0] := by
  simp only [matrixMap, demazure, map_neg, map_mul, Family.lift_crossing,
    Family.lift_dot, matrixFamily]
  decide

@[simp] theorem matrixMap_zeroHecke :
    matrixMap (zeroHecke 0 0) = !![0, 0; 0, 1] := by
  simp only [matrixMap, zeroHecke, map_mul, Family.lift_crossing,
    Family.lift_dot, matrixFamily]
  decide

theorem demazure_ne_zero : demazure 0 0 ≠ 0 := by
  intro h
  have hm := congrArg matrixMap h
  rw [matrixMap_demazure, map_zero] at hm
  have := congrArg (fun M : Mat => M 0 0) hm
  norm_num at this

theorem zeroHecke_ne_zero : zeroHecke 0 0 ≠ 0 := by
  intro h
  have hm := congrArg matrixMap h
  rw [matrixMap_zeroHecke, map_zero] at hm
  have := congrArg (fun M : Mat => M 1 1) hm
  norm_num at this

theorem one_ne_zero : (1 : Presented 0) ≠ 0 := by
  intro h
  have hm := congrArg matrixMap h
  rw [map_one, map_zero] at hm
  have := congrArg (fun M : Mat => M 0 0) hm
  norm_num at this

example : projector 1 * projector 1 = projector 1 := projector_idempotent 1
example : demazure 1 0 * demazure 1 1 * demazure 1 0 =
    demazure 1 1 * demazure 1 0 * demazure 1 1 := demazure_braid 0 1 rfl

#print axioms Family.lift
#print axioms demazureProduct_reduced_eq
#print axioms projector_idempotent
#print axioms map_projector_idempotent
#print axioms demazure_ne_zero

end OddMath.EvenNilHecke.Examples

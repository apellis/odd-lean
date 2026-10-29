import OddMath.QuiverHecke.HalfTurn.Mirror
import OddMath.SKM.MixedCrossingLocalExamples

/-! The reflection of the quiver Hecke supercategory on a concrete two-odd-colour datum. -/

noncomputable section
namespace NonVacuity.QuiverHeckeMirror
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open OddMath.SKM (Scalars)

private abbrev D₂ := OddMath.SKM.MixedCrossingLocalExamples.oddDatum
private def sc : Scalars D₂ ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)

example : (mirrorFunctor D₂ sc).obj ((pres D₂ sc).obj (ob D₂ [false, true])) =
    (pres D₂ sc).obj (ob D₂ [true, false]) :=
  mirrorFunctor_obj D₂ sc [false, true]

example (r : Rel D₂) : (mirrorLin D₂ sc).map ((pres D₂ sc).rel r) = 0 := mirror_rel D₂ sc r

end NonVacuity.QuiverHeckeMirror

#print axioms OddMath.QuiverHecke.mirrorFunctor
#print axioms OddMath.QuiverHecke.mirror_rel

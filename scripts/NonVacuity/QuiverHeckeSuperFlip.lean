import OddMath.QuiverHecke.HalfTurn.SuperFlip
import OddMath.SKM.MixedCrossingLocalExamples

/-! The reflection in a horizontal axis on a concrete two-odd-colour datum. -/

noncomputable section
namespace NonVacuity.QuiverHeckeSuperFlip
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

example (r : Rel D₂) : (flipFree D₂ sc).map ((pres D₂ sc).rel r) = 0 := flip_rel D₂ sc r

example : (pres D₂ sc).Presented ⥤ SOp ℚ (pres D₂ (parameterTwist D₂ sc)).Presented :=
  flipFunctor D₂ sc

end NonVacuity.QuiverHeckeSuperFlip

#print axioms OddMath.QuiverHecke.flipFunctor
#print axioms OddMath.QuiverHecke.flip_rel

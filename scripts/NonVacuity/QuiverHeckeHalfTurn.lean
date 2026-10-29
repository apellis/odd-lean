import OddMath.QuiverHecke.HalfTurn.Composite
import OddMath.SKM.MixedCrossingLocalExamples

/-! The half-turn `U` on a concrete two-odd-colour datum: the crossing weight `ε_ij`. -/

noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurn
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

example : (pres D₂ sc).Presented ⥤ SOp ℚ (pres D₂ (parameterTwist D₂ sc)).Presented :=
  halfTurnFunctor D₂ sc

/-- An equal-colour crossing in context goes to `-1` times the reflected crossing. -/
example (i : Bool) : halfTurnWeight (k := ℚ) (Shape.cross i i) = -1 := by
  simp [halfTurnWeight]

example (u v : List Bool) (i j : Bool) :=
  halfTurn_cross D₂ sc u i j v

end NonVacuity.QuiverHeckeHalfTurn

#print axioms OddMath.QuiverHecke.halfTurn_mkD
#print axioms OddMath.QuiverHecke.halfTurn_cross

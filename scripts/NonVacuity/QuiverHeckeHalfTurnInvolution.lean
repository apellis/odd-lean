import OddMath.QuiverHecke.HalfTurn.Involution
import OddMath.SKM.MixedCrossingLocalExamples

/-! The half-turn `U` is a linear isomorphism of coefficient-extended Hom spaces, on a concrete
two-odd-colour datum. -/

noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnInvolution
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

/-- The half-turn is bijective on the words `[true, false] → [false, true]`. -/
example : Function.Bijective (htCoef D₂ sc [true, false] [false, true]) :=
  htCoef_bijective D₂ sc [true, false] [false, true]

/-- Half-turning twice is the identity, up to the transports. -/
example (x : coefficientObj D₂ sc [true, false] ⟶ coefficientObj D₂ sc [false, true]) :
    htCoef D₂ (parameterTwist D₂ sc) [true, false] [false, true]
        (htCoef D₂ sc [true, false] [false, true] x) =
      scalarsCast D₂ (parameterTwist_involutive D₂ sc).symm rfl rfl x :=
  htCoef_htCoef D₂ sc x

end NonVacuity.QuiverHeckeHalfTurnInvolution

#print axioms OddMath.QuiverHecke.htCoef_htCoef
#print axioms OddMath.QuiverHecke.htCoef_bijective

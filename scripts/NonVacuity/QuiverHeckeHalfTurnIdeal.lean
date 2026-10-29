import OddMath.QuiverHecke.HalfTurn.CornerIdeal
import OddMath.SKM.MixedCrossingLocalExamples

/-! The half-turn `U` maps the transformed ideal into the ELV relation span, on a concrete
two-odd-colour datum. -/

noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnIdeal
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

/-- `U(K_2) ⊆ I_2` on the words `[true, false] → [true, false]`. -/
example : (TransformedIdeal D₂ sc (fun _ => 2) ∅ [true, false] [true, false]).map
    (htCoef D₂ sc [true, false] [true, false]) ≤
    ELVRelationSpan D₂ (parameterTwist D₂ sc) (fun _ => 2) [false, true] [false, true] :=
  htCoef_transformedIdeal_le D₂ sc (fun _ => 2) [true, false] [true, false]

/-- The half-turn of the last-strand dot power `y_last^3` on the word `[false, true]`. -/
example := htPres_lastDotPower D₂ sc [false] true 3

end NonVacuity.QuiverHeckeHalfTurnIdeal

#print axioms OddMath.QuiverHecke.htCoef_transformedIdeal_le
#print axioms OddMath.QuiverHecke.htPres_lastDotPower

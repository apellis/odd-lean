import OddMath.QuiverHecke.HalfTurn.IdealIdentification
import OddMath.SKM.MixedCrossingLocalExamples

/-! The half-turn `U` identifies the transformed ideal with the ELV relation span, on a concrete
two-odd-colour datum. -/

noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnIdealIdentification
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

/-- `U⁻¹(I_2) = K_2` on the words `[true, false] → [true, false]`. -/
example : (ELVRelationSpan D₂ (parameterTwist D₂ sc) (fun _ => 2) [false, true]
      [false, true]).comap (htCoef D₂ sc [true, false] [true, false]) =
    TransformedIdeal D₂ sc (fun _ => 2) ∅ [true, false] [true, false] :=
  comap_htCoef_elvRelationSpan D₂ sc (fun _ => 2) [true, false] [true, false]

/-- `U(I_3) ⊆ K_3` for the twisted parameters. -/
example : (ELVRelationSpan D₂ sc (fun _ => 3) [true, true] [true, true]).map
    (htCoef D₂ sc [true, true] [true, true]) ≤
    TransformedIdeal D₂ (parameterTwist D₂ sc) (fun _ => 3) ∅ [true, true] [true, true] :=
  htCoef_elvRelationSpan_le D₂ sc (fun _ => 3) [true, true] [true, true]

/-- The half-turn of the first-strand dot power `y_first^3` on the word `[true, false]`. -/
example := htPres_firstDotPower D₂ sc [false] true 3

end NonVacuity.QuiverHeckeHalfTurnIdealIdentification

#print axioms OddMath.QuiverHecke.comap_htCoef_elvRelationSpan
#print axioms OddMath.QuiverHecke.map_htCoef_transformedIdeal

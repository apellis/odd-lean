import OddMath.QuiverHecke.HalfTurn.CoefficientGenerators
import OddMath.SKM.MixedCrossingLocalExamples

/-! The half-turn `U` identifies `K_(N,T)` with `I_N + (T)` for a set `T` of homogeneous
coefficients of both parities, on a concrete two-odd-colour datum. -/

noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnCoefficientGenerators
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

private def oddTrue : {i : Bool // D₂.parity i = 1} := ⟨true, rfl⟩

/-- An even and an odd coefficient. -/
private def T : Set (OddMath.SKM.SYM D₂ ℚ) :=
  {OddMath.SKM.SYM.e D₂ ℚ true 1, OddMath.SKM.SYM.delta D₂ ℚ oddTrue}

private theorem hT : ∀ a ∈ T, ∃ q, CoefParity D₂ q a := by
  rintro a (rfl | rfl)
  · exact ⟨0, coefParity_e D₂ true 1⟩
  · exact ⟨1, coefParity_delta D₂ oddTrue⟩

/-- `U⁻¹(I_2 + (T)) = K_(2,T)` on the words `[true, false] → [true, false]`. -/
example : (ELVRelationSpan D₂ (parameterTwist D₂ sc) (fun _ => 2) [false, true] [false, true] ⊔
      CoefficientGeneratorSpan D₂ (parameterTwist D₂ sc) T [false, true] [false, true]).comap
        (htCoef D₂ sc [true, false] [true, false]) =
    TransformedIdeal D₂ sc (fun _ => 2) T [true, false] [true, false] :=
  comap_htCoef_elvRelationSpan_sup D₂ sc (fun _ => 2) T hT [true, false] [true, false]

/-- `K_(3,T) = K_3 + (T)`. -/
example : TransformedIdeal D₂ sc (fun _ => 3) T [true, true] [true, true] =
    TransformedIdeal D₂ sc (fun _ => 3) ∅ [true, true] [true, true] ⊔
      CoefficientGeneratorSpan D₂ sc T [true, true] [true, true] :=
  transformedIdeal_eq_sup D₂ sc (fun _ => 3) T [true, true] [true, true]

end NonVacuity.QuiverHeckeHalfTurnCoefficientGenerators

#print axioms OddMath.QuiverHecke.comap_htCoef_elvRelationSpan_sup
#print axioms OddMath.QuiverHecke.map_htCoef_transformedIdeal_sup

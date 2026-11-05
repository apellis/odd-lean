import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoefficients
import OddMath.QuiverHecke.ReservoirSourceCoordinates

/-! # Source quotient classes of actual regular-power word vectors

SwappedVacuumCoordinates §§5–7: the proved full half-turn kernel gives a
linear equivalence from the literal transformed source quotient onto every
vector of the actual regular-power word module. Its inverse intertwines
the existing signed old-Hom maps with chronological source composition,
and sends the literal coefficient action on the word unit to its source
class. This is a quotient-coordinate input, not a swapped action record.
-/
noncomputable section
namespace OddMath.QuiverHecke.PowerWordQuotientCoordinates
open CategoryTheory StringDiagrams Supercategory
open ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The actual balanced word vectors are all reached by the full source
half-turn; the old quotient and balanced generator are both surjective. -/
theorem surjective (s t : List I) :
    Function.Surjective (powerWordHalfTurnCoordinate D Sc cutoff L s t) := by
  rw [powerWordHalfTurnCoordinate_eq]
  change Function.Surjective (fun x =>
    powerWordGenerator D (parameterTwist D Sc) cutoff L t.reverse (OldCategory.mk s.reverse)
      ((ideal D (parameterTwist D Sc) cutoff t.reverse s.reverse).mkQ
        (elvQuotientMap D (parameterTwist D Sc) cutoff _ _ (htCoef D Sc s t x))))
  exact (powerWordGenerator_surjective D (parameterTwist D Sc) cutoff L t.reverse _).comp
    ((Submodule.mkQ_surjective _).comp
      ((elvQuotientMap_surjective D (parameterTwist D Sc) cutoff t.reverse s.reverse).comp
        (htCoefEquiv D Sc s t).surjective))

/-- The literal transformed ideal, with the unchanged elementary powers. -/
abbrev kernel (s t : List I) := TransformedIdeal D Sc cutoff
  (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) s t

/-- Exact source quotient coordinates on all actual regular-power word
vectors, obtained from the proved kernel rather than a faithfulness premise. -/
def quotientEquiv (s t : List I) :
    ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸ kernel D Sc cutoff L s t) ≃ₗ[k]
      (powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj (OldCategory.mk s.reverse) :=
  (Submodule.quotEquivOfEq _ _ (powerWordHalfTurnCoordinate_ker D Sc cutoff L s t).symm).trans
    ((powerWordHalfTurnCoordinate D Sc cutoff L s t).quotKerEquivOfSurjective
      (surjective D Sc cutoff L s t))

theorem quotientEquiv_mk (s t : List I) (y : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    quotientEquiv D Sc cutoff L s t ((kernel D Sc cutoff L s t).mkQ y) =
      powerWordHalfTurnCoordinate D Sc cutoff L s t y := by
  change quotientEquiv D Sc cutoff L s t (Submodule.Quotient.mk y) = _
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Pull an actual word vector back to its uniquely determined transformed
source quotient class. -/
def coordinate (s t : List I) :
    (powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj (OldCategory.mk s.reverse) →ₗ[k]
      ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸ kernel D Sc cutoff L s t) :=
  (quotientEquiv D Sc cutoff L s t).symm.toLinearMap

theorem coordinate_mk (s t : List I) (y : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    coordinate D Sc cutoff L s t (powerWordHalfTurnCoordinate D Sc cutoff L s t y) =
      (kernel D Sc cutoff L s t).mkQ y := by
  apply (quotientEquiv D Sc cutoff L s t).injective
  rw [quotientEquiv_mk]
  exact (quotientEquiv D Sc cutoff L s t).apply_symm_apply _

/-- The two signed opposite compositions cancel on all coefficient
vectors, including inhomogeneous source arrows. -/
theorem sourceMap_apply_coordinate {s t r : List I}
    (b : coefficientObj D Sc s ⟶ coefficientObj D Sc t)
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc r) :
    (PowerWordComposition.sourceMap D Sc cutoff L t r g).total (OldCategory.mk s.reverse)
      (powerWordHalfTurnCoordinate D Sc cutoff L s t b) =
    powerWordHalfTurnCoordinate D Sc cutoff L s r (b ≫ g) := by
  have h := PowerWordComposition.sourceMap_evaluate D Sc cutoff L s r (b ≫ g)
  rw [PowerWordComposition.sourceMap_comp] at h
  change (PowerWordComposition.sourceMap D Sc cutoff L s t b ≫
    PowerWordComposition.sourceMap D Sc cutoff L t r g).total (OldCategory.mk s.reverse)
      (PowerWordYoneda.unitVector D (parameterTwist D Sc) cutoff L s.reverse) = _ at h
  rw [Superfunctor.comp_total, SVec.comp_apply] at h
  have hb := PowerWordComposition.sourceMap_evaluate D Sc cutoff L s t b
  change (PowerWordComposition.sourceMap D Sc cutoff L s t b).total (OldCategory.mk s.reverse)
    (PowerWordYoneda.unitVector D (parameterTwist D Sc) cutoff L s.reverse) = _ at hb
  rw [hb] at h
  exact h

/-- The source-class square for the actual old-Hom map on every actual
word vector. Its only premise specifies the input quotient class. -/
theorem coordinate_action {s t r : List I}
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc r)
    (v : (powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj (OldCategory.mk s.reverse))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc t)
    (hy : coordinate D Sc cutoff L s t v = (kernel D Sc cutoff L s t).mkQ y) :
    coordinate D Sc cutoff L s r
      ((PowerWordComposition.sourceMap D Sc cutoff L t r g).total (OldCategory.mk s.reverse) v) =
      (kernel D Sc cutoff L s r).mkQ (y ≫ g) := by
  have hv : v = powerWordHalfTurnCoordinate D Sc cutoff L s t y :=
    (quotientEquiv D Sc cutoff L s t).symm.injective
      (hy.trans (coordinate_mk D Sc cutoff L s t y).symm)
  rw [hv, sourceMap_apply_coordinate, coordinate_mk]

/-- The half-turn fixes full coefficients on the literal old word, not
only their even scalar part. -/
theorem halfTurnOldHom_coefficient (s : List I) (a : SKM.SYM D k) :
    halfTurnOldHom D Sc cutoff s s (sourceCoefficientHom D Sc a (𝟙 _)) =
      coefficientEndomorphism D (parameterTwist D Sc) cutoff s.reverse
        (SKM.SYM.elvCoefficientQuotient D cutoff a) := by
  change sourceToOldHom D (parameterTwist D Sc) cutoff s.reverse s.reverse
    (htCoef D Sc s s (sourceCoefficientHom D Sc a (𝟙 _))) = _
  rw [htCoef_sourceCoefficientHom, htPres_id]
  change (ideal D (parameterTwist D Sc) cutoff s.reverse s.reverse).mkQ
    (elvQuotientMap D (parameterTwist D Sc) cutoff _ _ (sourceCoefficientHom _ _ a (𝟙 _))) = _
  rw [elvQuotientMap_source]
  rfl

/-- Source coefficient insertion is the given full coefficient module
action on the actual regular-power word, with no coordinate-defined replacement. -/
theorem sourceCoefficient_action (s : List I) (a : SKM.SYM D k) :
    PowerWordComposition.sourceMap D Sc cutoff L s s (sourceCoefficientHom D Sc a (𝟙 _)) =
      coefficientModuleAction D (parameterTwist D Sc) cutoff
        (powerWordModule D (parameterTwist D Sc) cutoff L s.reverse)
        (SKM.SYM.elvCoefficientQuotient D cutoff a) := by
  rw [PowerWordComposition.sourceMap_apply, halfTurnOldHom_coefficient,
    ← PowerWordCoefficients.coefficient_fromArrow]

/-- Literal coefficient insertion on the selected word unit has its
unchanged full source quotient class. -/
theorem coefficient_unit_class (s : List I) (a : SKM.SYM D k) :
    coordinate D Sc cutoff L s s
      ((coefficientModuleAction D (parameterTwist D Sc) cutoff
        (powerWordModule D (parameterTwist D Sc) cutoff L s.reverse)
        (SKM.SYM.elvCoefficientQuotient D cutoff a)).total (OldCategory.mk s.reverse)
        (PowerWordYoneda.unitVector D (parameterTwist D Sc) cutoff L s.reverse)) =
      (kernel D Sc cutoff L s s).mkQ (sourceCoefficientHom D Sc a (𝟙 _)) := by
  rw [← sourceCoefficient_action]
  have h := PowerWordComposition.sourceMap_evaluate D Sc cutoff L s s (sourceCoefficientHom D Sc a (𝟙 _))
  change (PowerWordComposition.sourceMap D Sc cutoff L s s (sourceCoefficientHom D Sc a (𝟙 _))).total
    (OldCategory.mk s.reverse) (PowerWordYoneda.unitVector D (parameterTwist D Sc) cutoff L s.reverse) = _ at h
  rw [h, coordinate_mk]

end OddMath.QuiverHecke.PowerWordQuotientCoordinates

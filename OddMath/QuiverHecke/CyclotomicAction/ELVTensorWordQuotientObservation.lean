import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWords
import OddMath.QuiverHecke.HalfTurn.PowerWordQuotientCoordinates

/-! # Source quotient observation of tensor word values

SwappedVacuumCoordinates §§3–7: evaluate the selected tensor-word value
on its canonical cyclic source unit and use the exact full half-turn
kernel to recover its source quotient class. This intermediate map is
on regular-probe value Homs; attaching the supported matrix row requires
its canonical original-weight transport.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.TensorVacuumWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X) (s t : List I)
local notation "Tw" => parameterTwist D Sc
local notation "R" => WeightTensorVacuum.regularProbe D Tw m ΛP

/-- The full source quotient class of a whole map on the selected regular
probe value. Both the cyclic evaluation and the kernel are already proved. -/
def quotientObservation :
    ((wordHom D Tw m cutoff L ΛP ΛR s.reverse).obj R ⟶
      PowerWordWeight.wordFamily D Tw cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR s.reverse) t.reverse) ≃ₗ[k]
    ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸
      PowerWordQuotientCoordinates.kernel D Sc cutoff L s t) :=
  (homEquiv D Tw m cutoff L ΛP ΛR s.reverse t.reverse).trans
    (PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s t).symm

/-- The source vector is the literal old-word unit pulled back through
the prescribed global chart of the tensor word. -/
def sourceUnit :
    (((wordHom D Tw m cutoff L ΛP ΛR s.reverse).obj R)
      (PowerWordWeight.wordBlock D ΛR s.reverse)).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl) :=
  (moduleIsoLinearEquiv (Pi.isoApp (chart D Tw m cutoff L ΛP ΛR s.reverse)
    (PowerWordWeight.wordBlock D ΛR s.reverse))
    (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)).symm
      (PowerWordYoneda.unitVector D Tw cutoff L s.reverse)

/-- The global source chart gives the same unit as the native word-value
chart after the prescribed tensor-vacuum comparison. -/
theorem sourceUnit_eq_valueIso :
    sourceUnit D Sc m cutoff L ΛP ΛR s =
      (((valueIso D Tw m cutoff L ΛP ΛR s.reverse).inv)
        (PowerWordWeight.wordBlock D ΛR s.reverse)).total
        (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
        (PowerWordHomCoordinates.unitVector D Tw cutoff L ΛR s.reverse) := by
  change (((PowerWordEvaluation.chart D Tw cutoff L ΛR s.reverse).inv
      (PowerWordWeight.wordBlock D ΛR s.reverse) ≫
        (valueIso D Tw m cutoff L ΛP ΛR s.reverse).inv
          (PowerWordWeight.wordBlock D ΛR s.reverse)).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
              (PowerWordYoneda.unitVector D Tw cutoff L s.reverse) = _
  rw [Superfunctor.comp_total]
  rfl

/-- The observation is literal evaluation on the canonical source unit,
followed by the exact quotient coordinate, on every full value-Hom arrow. -/
theorem quotientObservation_apply
    (f : (wordHom D Tw m cutoff L ΛP ΛR s.reverse).obj R ⟶
      PowerWordWeight.wordFamily D Tw cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR s.reverse) t.reverse) :
    quotientObservation D Sc m cutoff L ΛP ΛR s t f =
      PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t
        ((f (PowerWordWeight.wordBlock D ΛR s.reverse)).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          (sourceUnit D Sc m cutoff L ΛP ΛR s)) := by
  change PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t
    (homEquiv D Tw m cutoff L ΛP ΛR s.reverse t.reverse f) = _
  congr 1
  change ((((valueIso D Tw m cutoff L ΛP ΛR s.reverse).inv ≫ f) ≫ 𝟙 _)
    (PowerWordWeight.wordBlock D ΛR s.reverse)).total
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
      (PowerWordHomCoordinates.unitVector D Tw cutoff L ΛR s.reverse) = _
  rw [Category.comp_id]
  change (((valueIso D Tw m cutoff L ΛP ΛR s.reverse).inv
    (PowerWordWeight.wordBlock D ΛR s.reverse) ≫ f (PowerWordWeight.wordBlock D ΛR s.reverse)).total
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
        (PowerWordHomCoordinates.unitVector D Tw cutoff L ΛR s.reverse) = _
  rw [Superfunctor.comp_total, sourceUnit_eq_valueIso]
  rfl

/-- The quotient observation retains every map of the regular-probe value. -/
theorem quotientObservation_injective : Function.Injective
    (quotientObservation D Sc m cutoff L ΛP ΛR s t) :=
  (quotientObservation D Sc m cutoff L ΛP ΛR s t).injective

end OddMath.QuiverHecke.ELVOld.TensorVacuumWords

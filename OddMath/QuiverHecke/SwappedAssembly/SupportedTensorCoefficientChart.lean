import OddMath.QuiverHecke.CyclotomicAction.ELVTensorWordCoefficientChart
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorUnitObservation

/-! # Full coefficients in the supported path chart

SwappedVacuumCoordinates §§6–7: the actual original-weight reservoir
path chart intertwines the direct full-input source coefficient action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
/-- A coefficient square before evaluation in an arbitrary actual Hom. -/
def tensorCoefficientSquare {k : Type u} [CommRing k]
    {A C : PiSCat.{u,u,u + 1} k} (F : A ⟶ C) (R₀ : A) (f : End F)
    {T : C} (e : F.obj R₀ ⟶ T) (z : End T) : Prop :=
  f.total R₀ ≫ e = e ≫ z

private theorem pathSquareTransfer {k J I : Type u} [CommRing k]
    (A : PiSCat.{u,u,u + 1} k) (C : J → PiSCat.{u,u,u + 1} k)
    (W : (x : J) → List I → C x) (z : ∀ x ν, End (W x ν))
    {x y : J} (h : x = y) (F : A ⟶ C x) (G : A ⟶ C y) (hFG : HEq F G)
    (f : End F) (g : End G) (hfg : HEq f g) (R₀ : A) (ν : List I)
    (eF : F.obj R₀ ⟶ W x ν) (eG : G.obj R₀ ⟶ W y ν) (he : HEq eF eG)
    (hs : tensorCoefficientSquare G R₀ g eG (z y ν)) :
    tensorCoefficientSquare F R₀ f eF (z x ν) := by
  subst y
  cases hFG
  cases hfg
  cases he
  exact hs

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP

/-- The unchanged signed coefficient arrow, with its whole-family target explicit. -/
def tensorWordCoefficientArrow (x : X) (ν : List I) (a : SYM D k) :
    End (show elvWeightSpace D Tw cutoff N ΛR x from
      PowerWordWeight.wordFamily D Tw cutoff L ΛR x ν) :=
  PowerWordWeightWhiskering.wordFamilyArrow D Tw cutoff L ΛR x ν ν
    (coefficientEndomorphism D Tw cutoff ν (SYM.elvCoefficientQuotient D cutoff a))

attribute [local irreducible] tensorWordCoefficientArrow tensorPathValueChart

/-- Every original-weight path vector satisfies the same coefficient square. -/
theorem tensorPathCoefficient_square_apply {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hup : ∀ b ∈ l, b.l.1 = true) (a : SYM D k)
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR c))
    (w : ContentCategory D Tw cutoff N β.1)
    (v : (((TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup).obj R₀) β).obj w) :
    ((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom β).total w
      ((((VacuumTensorCoefficientMaps.pathCoefficientAction D Tw m cutoff L ΛP ΛR p hup a).total R₀) β).total w v) =
    (tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR c)
        (l.map (fun b => b.l.2)).reverse a β).total w
      (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom β).total w v) := by
  have hw := TensorReservoirWords.path_weight D ΛR p hup
  have hF := TensorReservoirWords.pathHom_heq D (parameterTwist D Sc) m cutoff L ΛP ΛR p hup
  have hf := TensorPathCoefficientCoherence.pathAction_heq D (parameterTwist D Sc) m cutoff L ΛP ΛR p hup a
  have he := tensorPathValueChart_global_heq D Sc m cutoff ΛP ΛR L p hup
  generalize heChart : (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom = e at he ⊢
  clear heChart
  generalize hν : (l.map (fun b => b.l.2)).reverse = ν at hw hF hf e he ⊢
  have hs := pathSquareTransfer (probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP))
    (fun x => elvWeightSpace D (parameterTwist D Sc) cutoff (PowerWordContent.powerBound D cutoff L) ΛR x)
    (PowerWordWeight.wordFamily D (parameterTwist D Sc) cutoff L ΛR)
    (fun x ν => tensorWordCoefficientArrow D Sc cutoff ΛR L x ν a) hw
    (TensorReservoirWords.pathHom D (parameterTwist D Sc) m cutoff L ΛP ΛR p hup)
    (TensorVacuumWords.wordHom D (parameterTwist D Sc) m cutoff L ΛP ΛR ν) hF
    (VacuumTensorCoefficientMaps.pathCoefficientAction D (parameterTwist D Sc) m cutoff L ΛP ΛR p hup a)
    (TensorWordCoefficientAction.wordAction D (parameterTwist D Sc) m cutoff L ΛP ΛR ν a) hf (WeightTensorVacuum.regularProbe D (parameterTwist D Sc) m ΛP) ν
    e
    (TensorVacuumWords.chart D (parameterTwist D Sc) m cutoff L ΛP ΛR ν).hom he
    (by
      unfold tensorCoefficientSquare tensorWordCoefficientArrow
      exact TensorWordCoefficientChart.chart_square D (parameterTwist D Sc) m cutoff L ΛP ΛR ν a)

  unfold tensorCoefficientSquare at hs
  have h := congrArg (fun f => (f β).total w v) hs
  change (((VacuumTensorCoefficientMaps.pathCoefficientAction D Tw m cutoff L ΛP ΛR p hup a).total R₀ β ≫
    e β).total w) v =
      ((e β ≫
        tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR c)
        ν a β).total w) v at h
  simpa only [Superfunctor.comp_total, SVec.comp_apply] using h
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

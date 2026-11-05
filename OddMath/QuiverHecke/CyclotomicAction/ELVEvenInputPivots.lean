import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputOperators
import OddMath.QuiverHecke.CyclotomicAction.ELVCapInputRecurrence

/-! # Cap pivots on even boundary lifts

The parity-zero input pivots in DeformedRouquierMatrix, section 4.
Decoded moving dots shift the ordinary long coordinates. The raw cap reads
the constant coefficient of the next boundary row. The actual arbitrary-Hom
leading theorem therefore gives the anti-diagonal unit and below-diagonal
vanishing, with every old coefficient and balance twist retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenLiftBoundary (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff i v (t ++ [i]) :=
  (pMap D Sc cutoff i v (t ++ [i])).comp (offDiagonalLongSection D Sc cutoff p i v t)

theorem evenLiftBoundary_shift (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    evenLiftBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) =
      appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
        (evenLiftBoundary D Sc cutoff p i v t f) := by
  change pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t _) = _
  rw [← evenMoving_offDiagonalLongSection D Sc cutoff p i hi, pMap_movingEvenDot D Sc cutoff i hi]
  rfl

def evenBoundaryCrossCoordinates (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] ShortTarget D Sc cutoff i v t :=
  (ShortCrossCoordinates.decode D Sc cutoff i v t).comp (evenLiftBoundary D Sc cutoff p i v t)

theorem evenCrossingInputDotAffine_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    evenCrossingInputDotAffine D Sc cutoff i v t (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) =
      evenBoundaryCrossCoordinates D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) := by
  change ShortCrossCoordinates.decode D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (shortCross D Sc cutoff i v t
        (ShortCrossCoordinates.decode D Sc cutoff i v t (evenLiftBoundary D Sc cutoff p i v t f)))) = _
  rw [shortCross_decode_residual, map_sub, appendMovingPowerTarget_embedding_one,
    map_sub, ShortCrossCoordinates.decode_embedding, sub_zero, ← evenLiftBoundary_shift D Sc cutoff p i hi]
  rfl

theorem evenInputContractionAffine_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    evenInputContractionAffine D Sc cutoff i v t (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) 0 := by
  change appendC0InputDefect D Sc cutoff i v t
    (shortCross D Sc cutoff i v t
      (ShortCrossCoordinates.decode D Sc cutoff i v t (evenLiftBoundary D Sc cutoff p i v t f))) 0 = _
  rw [shortCross_decode_residual, map_sub, appendC0InputDefect_embedding, sub_zero]
  change (appendC0 D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (evenLiftBoundary D Sc cutoff p i v t f)) -
    appendInputShift D Sc cutoff i v t
      (appendC0 D Sc cutoff i v t (evenLiftBoundary D Sc cutoff p i v t f))) 0 = _
  rw [Finsupp.sub_apply, appendInputShift_zero, sub_zero, ← evenLiftBoundary_shift D Sc cutoff p i hi]
  rfl

theorem evenCrossingInputDotAffine_iterate_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (r : ℕ) (f : ℕ →₀ Old D Sc cutoff v t) :
    (evenCrossingInputDotAffine D Sc cutoff i v t)^[r] (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) =
      evenBoundaryCrossCoordinates D Sc cutoff p i v t ((evenLongShift D Sc cutoff v t)^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      evenCrossingInputDotAffine_boundaryCrossCoordinates D Sc cutoff p i hi,
      Function.iterate_succ_apply']

/-- The raw cap after r input dots reads row r+d+1 at degree zero. -/
theorem evenInputContractionAffine_iterate_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (r d : ℕ) (b : Old D Sc cutoff v t) :
    evenInputContractionAffine D Sc cutoff i v t
      ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r]
        (evenBoundaryCrossCoordinates D Sc cutoff p i v t (Finsupp.single d b))) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single (r + d + 1) b) 0 := by
  rw [evenCrossingInputDotAffine_iterate_boundaryCrossCoordinates D Sc cutoff p i hi,
    evenInputContractionAffine_boundaryCrossCoordinates D Sc cutoff p i hi,
    evenLongShift_iterate_single, evenLongShift_single]

theorem evenInputContractionAffine_below (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (r d : ℕ) (b : Old D Sc cutoff v t)
    (h : r + d + 1 + endpointQPDegree D cutoff i v < outputSDegree D i v) :
    evenInputContractionAffine D Sc cutoff i v t
      ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r]
        (evenBoundaryCrossCoordinates D Sc cutoff p i v t (Finsupp.single d b))) = 0 := by
  rw [evenInputContractionAffine_iterate_boundaryCrossCoordinates D Sc cutoff p i hi]
  exact offDiagonalBoundary_even_above D Sc cutoff p i hi v t (r + d + 1) 0 b (by omega)

theorem evenInputContractionAffine_pivot (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (r d : ℕ) (b : Old D Sc cutoff v t)
    (h : outputSDegree D i v = r + d + 1 + endpointQPDegree D cutoff i v) :
    evenInputContractionAffine D Sc cutoff i v t
      ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r]
        (evenBoundaryCrossCoordinates D Sc cutoff p i v t (Finsupp.single d b))) =
      evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t b := by
  rw [evenInputContractionAffine_iterate_boundaryCrossCoordinates D Sc cutoff p i hi]
  exact offDiagonalBoundary_even_top D Sc cutoff p i hi v t (r + d + 1) 0 b (by omega)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor


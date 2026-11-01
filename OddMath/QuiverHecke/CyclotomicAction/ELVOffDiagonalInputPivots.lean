import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputOperators
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundaryLeading

/-! # Input contraction pivots on the actual boundary lifts

These are the cap pivots used by DeformedRouquierMatrix, section 4.
The input shift has zero constant coefficient. Hence the actual contraction
of a decoded lift is the constant coefficient of the next boundary value.
This gives anti-diagonal vanishing and the prescribed leading equivalence.
These statements concern the prescribed input operators on arbitrary old
Hom coefficients. Their categorical counit/dot comparison remains separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def offDiagonalLiftBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff j.1 v (t ++ [j.1]) :=
  (pMap D Sc cutoff j.1 v (t ++ [j.1])).comp
    (offDiagonalLongSection D Sc cutoff p j.1 v t)

theorem offDiagonalLiftBoundary_rho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalLiftBoundary D Sc cutoff p j v t
      (offDiagonalCoefficientRho D Sc cutoff p j v t f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (offDiagonalLiftBoundary D Sc cutoff p j v t f) := by
  change pMap D Sc cutoff j.1 v (t ++ [j.1])
    (offDiagonalLongSection D Sc cutoff p j.1 v t _) = _
  rw [← boundaryRho_offDiagonalLongSection, pMap_boundaryRho]
  rfl

def offDiagonalBoundaryCrossCoordinates (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] ShortTarget D Sc cutoff j.1 v t :=
  (ShortCrossCoordinates.decode D Sc cutoff j.1 v t).comp
    (offDiagonalLiftBoundary D Sc cutoff p j v t)

theorem offDiagonalCrossingInputDotAffine_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalCrossingInputDotAffine D Sc cutoff j v t (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) =
      offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v t
        (ShortCrossCoordinates.decode D Sc cutoff j.1 v t (offDiagonalLiftBoundary D Sc cutoff p j v t f)))) = _
  rw [shortCross_decode_residual, map_sub, appendMovingPowerTarget_embedding_one,
    map_sub, ShortCrossCoordinates.decode_embedding, sub_zero,
    ← offDiagonalLiftBoundary_rho]
  rfl

theorem offDiagonalInputContractionAffine_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalInputContractionAffine D Sc cutoff j v t (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (offDiagonalCoefficientRho D Sc cutoff p j v t f) 0 := by
  change appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t
      (ShortCrossCoordinates.decode D Sc cutoff j.1 v t (offDiagonalLiftBoundary D Sc cutoff p j v t f))) 0 = _
  rw [shortCross_decode_residual, map_sub, appendC0InputDefect_embedding, sub_zero]
  change (appendC0 D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (offDiagonalLiftBoundary D Sc cutoff p j v t f)) -
      appendInputShift D Sc cutoff j.1 v t
        (appendC0 D Sc cutoff j.1 v t (offDiagonalLiftBoundary D Sc cutoff p j v t f))) 0 = _
  rw [Finsupp.sub_apply, appendInputShift_zero, sub_zero, ← offDiagonalLiftBoundary_rho]
  rfl

theorem offDiagonalCrossingInputDotAffine_iterate_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    (offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r] (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) =
      offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
        ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      offDiagonalCrossingInputDotAffine_boundaryCrossCoordinates, Function.iterate_succ_apply']

theorem offDiagonalInputContractionAffine_corrected_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t) :
    offDiagonalInputContractionAffine D Sc cutoff j v t
      ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalLongExtraction D Sc cutoff p j.1 v t
          (offDiagonalCorrectedLift D Sc cutoff p j v t (r + d + 1) b)) 0 := by
  rw [offDiagonalCrossingInputDotAffine_iterate_boundaryCrossCoordinates,
    offDiagonalInputContractionAffine_boundaryCrossCoordinates]
  simp only [offDiagonalLongExtraction_correctedLift]
  rw [← Function.iterate_add_apply]
  have hs : (offDiagonalCoefficientRho D Sc cutoff p j v t)^[r + d + 1] (Finsupp.single 0 b) =
      offDiagonalCoefficientRho D Sc cutoff p j v t
        ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[r + d] (Finsupp.single 0 b)) :=
    Function.iterate_succ_apply' _ _ _
  rw [hs]

theorem offDiagonalInputContractionAffine_corrected_below (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t)
    (h : r + d + 1 + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) :
    offDiagonalInputContractionAffine D Sc cutoff j v t
      ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) = 0 := by
  rw [offDiagonalInputContractionAffine_corrected_iterate]
  exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t (r + d + 1) 0 b (by omega)

theorem offDiagonalInputContractionAffine_corrected_pivot (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t)
    (h : outputSDegree D j.1 v = r + d + 1 + endpointQPDegree D cutoff j.1 v) :
    offDiagonalInputContractionAffine D Sc cutoff j v t
      ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) =
      offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t 0 b := by
  rw [offDiagonalInputContractionAffine_corrected_iterate]
  exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t (r + d + 1) 0 b (by omega)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor


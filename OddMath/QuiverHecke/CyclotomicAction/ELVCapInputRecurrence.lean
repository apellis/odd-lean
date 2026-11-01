import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingInputDot
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading

/-! # Input contraction pivots on the actual boundary lifts

The input shift has zero constant coefficient. Hence the actual contraction
of a decoded lift is the constant coefficient of the next boundary value.
This gives anti-diagonal vanishing and the prescribed leading equivalence.
These statements concern the concrete input operators; categorical cap
comparison and the full factor action remain separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem appendInputShift_zero (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) : appendInputShift D Sc cutoff i v t f 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single m b => simp [appendInputShift, appendOutputShift]

def boundaryCrossCoordinates (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] ShortTarget D Sc cutoff j.1 v v :=
  (ShortCrossCoordinates.decode D Sc cutoff j.1 v v).comp
    (outputLiftBoundary D Sc cutoff p j v)

theorem crossingInputDotAffine_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    crossingInputDotAffine D Sc cutoff j v (boundaryCrossCoordinates D Sc cutoff p j v f) =
      boundaryCrossCoordinates D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v v
    (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v v
        (ShortCrossCoordinates.decode D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f)))) = _
  rw [shortCross_decode_residual, map_sub, appendMovingPowerTarget_embedding_one,
    map_sub, ShortCrossCoordinates.decode_embedding, sub_zero,
    ← outputLiftBoundary_rho]
  rfl

theorem inputContractionAffine_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    inputContractionAffine D Sc cutoff j v (boundaryCrossCoordinates D Sc cutoff p j v f) =
      outputPolynomialBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) 0 := by
  change appendC0InputDefect D Sc cutoff j.1 v v
    (shortCross D Sc cutoff j.1 v v
      (ShortCrossCoordinates.decode D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f))) 0 = _
  rw [shortCross_decode_residual, map_sub, appendC0InputDefect_embedding, sub_zero]
  have h := congrArg (fun z : ℕ →₀ Old D Sc cutoff v v => z 0)
    (outputPolynomialBoundary_rho D Sc cutoff p j v f)
  simp only [Finsupp.add_apply, appendInputShift_zero, zero_add, Finsupp.single_eq_same] at h
  exact h.symm

theorem crossingInputDotAffine_iterate_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (r : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    (crossingInputDotAffine D Sc cutoff j v)^[r] (boundaryCrossCoordinates D Sc cutoff p j v f) =
      boundaryCrossCoordinates D Sc cutoff p j v
        ((outputCoefficientRho D Sc cutoff p j v)^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      crossingInputDotAffine_boundaryCrossCoordinates, Function.iterate_succ_apply']

theorem inputContractionAffine_corrected_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (r d : ℕ)
    (b : Old D Sc cutoff v v) :
    inputContractionAffine D Sc cutoff j v
      ((crossingInputDotAffine D Sc cutoff j v)^[r]
        (boundaryCrossCoordinates D Sc cutoff p j v
          (outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v d b)))) =
      outputPolynomialBoundary D Sc cutoff p j v
        (outputLongExtraction D Sc cutoff p j.1 v
          (outputCorrectedLift D Sc cutoff p j v (r + d + 1) b)) 0 := by
  rw [crossingInputDotAffine_iterate_boundaryCrossCoordinates,
    inputContractionAffine_boundaryCrossCoordinates]
  simp only [outputLongExtraction_correctedLift]
  rw [← Function.iterate_add_apply]
  have hs : (outputCoefficientRho D Sc cutoff p j v)^[r + d + 1] (Finsupp.single 0 b) =
      outputCoefficientRho D Sc cutoff p j v
        ((outputCoefficientRho D Sc cutoff p j v)^[r + d] (Finsupp.single 0 b)) :=
    Function.iterate_succ_apply' _ _ _
  rw [hs]

theorem inputContractionAffine_corrected_below (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (r d : ℕ)
    (b : Old D Sc cutoff v v)
    (h : r + d + 1 + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) :
    inputContractionAffine D Sc cutoff j v
      ((crossingInputDotAffine D Sc cutoff j v)^[r]
        (boundaryCrossCoordinates D Sc cutoff p j v
          (outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v d b)))) = 0 := by
  rw [inputContractionAffine_corrected_iterate]
  exact outputBoundary_corrected_above D Sc cutoff p j v (r + d + 1) 0 b (by omega)

theorem inputContractionAffine_corrected_pivot (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (r d : ℕ)
    (b : Old D Sc cutoff v v)
    (h : outputSDegree D j.1 v = r + d + 1 + endpointQPDegree D cutoff j.1 v) :
    inputContractionAffine D Sc cutoff j v
      ((crossingInputDotAffine D Sc cutoff j v)^[r]
        (boundaryCrossCoordinates D Sc cutoff p j v
          (outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v d b)))) =
      outputBoundaryLeadingEquiv D Sc cutoff p j v 0 b := by
  rw [inputContractionAffine_corrected_iterate]
  exact outputBoundary_corrected_top D Sc cutoff p j v (r + d + 1) 0 b (by omega)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

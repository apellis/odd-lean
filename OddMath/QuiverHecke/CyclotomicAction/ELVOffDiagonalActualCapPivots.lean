import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapInput
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundarySnake
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRhoExtraction
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundaryLeading
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect

/-! # Actual cap pivots on arbitrary old Hom coefficients
The actual shifted counit and actual induction-dot/source-grading operator
agree with the concrete full-coefficient append formulas. Their values on
actual corrected source lifts give the boundary leading equivalence.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

@[simp] theorem coefficientOneSourceEquiv_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    coefficientOneSourceEquiv D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      tensor D Sc cutoff j.1 v s t g b := by
  simp [coefficientOneSourceEquiv, tensor, j.property]

theorem actualSourceInputContraction_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    actualSourceInputContraction D Sc cutoff j v t (tensor D Sc cutoff j.1 v s t g b) =
      oldComp D Sc cutoff v (s ++ [j.1]) t
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) g := by
  rw [← coefficientOneSourceEquiv_tensor, actualSourceInputContraction_carrier,
    actualShiftedInputContraction_tensor]

theorem actualSourceInputDot_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    actualSourceInputDot D Sc cutoff j v t (tensor D Sc cutoff j.1 v s t g b) =
      -tensor D Sc cutoff j.1 v s t
        (oldAppendDotComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g)
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) := by
  rw [← coefficientOneSourceEquiv_tensor, actualSourceInputDot_carrier,
    actualShiftedInputDot_tensor, map_neg, coefficientOneSourceEquiv_tensor]

def offDiagonalInputContractionAffine (j : {j : I // D.parity j = 1}) (v t : List I) :
    ShortTarget D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t where
  toFun z := appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t z) 0
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' a b := by simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

def offDiagonalInputDotAffine (j : {j : I // D.parity j = 1}) (v t : List I) :
    ShortTarget D Sc cutoff j.1 v t →ₗ[k] ShortTarget D Sc cutoff j.1 v t :=
  ShortCrossCoordinates.decode D Sc cutoff j.1 v t ∘ₗ
    appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1 ∘ₗ
      shortCross D Sc cutoff j.1 v t

theorem offDiagonalInputDotAffine_representative (j : {j : I // D.parity j = 1})
    (v s t : List I) (r : hom D Sc cutoff v (s ++ [j.1]))
    (g : hom D Sc cutoff (s ++ [j.1]) t) :
    offDiagonalInputDotAffine D Sc cutoff j v t
      (shortTensor D Sc cutoff j.1 v s t g ((ideal D Sc cutoff _ _).mkQ r)) =
      SKM.zsign k (D.parity j.1 * D.parity j.1) •
        shortTensor D Sc cutoff j.1 v s t
          (appendMovingPower D Sc cutoff j.1 s 1 ≫ g)
          ((ideal D Sc cutoff _ _).mkQ (twist k (D.parity j.1) r)) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v t
        (shortTensor D Sc cutoff j.1 v s t g ((ideal D Sc cutoff _ _).mkQ r)))) = _
  rw [ShortCrossCoordinates.column_mk, appendMovingPowerTarget_crossing_one]
  simp only [map_sub, map_smul, ShortCrossCoordinates.decode_embedding, smul_zero, sub_zero]
  rw [← ShortCrossCoordinates.column_mk, ShortCrossCoordinates.decode_shortCross]

theorem actualSourceInputContraction_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    actualSourceInputContraction D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      offDiagonalInputContractionAffine D Sc cutoff j v t z := by
  suffices h : (actualSourceInputContraction D Sc cutoff j v t).comp
      (q D Sc cutoff j.1 v t) = offDiagonalInputContractionAffine D Sc cutoff j v t from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change actualSourceInputContraction D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (shortTensor D Sc cutoff j.1 v s.word t g b)) = _
  rw [q_shortTensor, actualSourceInputContraction_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j.1])).mkQ_surjective b
  change _ = appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t
      (shortTensor D Sc cutoff j.1 v s.word t g ((ideal D Sc cutoff _ _).mkQ r))) 0
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same]
  change (ideal D Sc cutoff v t).mkQ (twist k 1 r ≫ g) = _
  simp [j.property, SKM.zsign]

theorem actualSourceInputDot_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    actualSourceInputDot D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t (offDiagonalInputDotAffine D Sc cutoff j v t z) := by
  suffices h : (actualSourceInputDot D Sc cutoff j v t).comp
      (q D Sc cutoff j.1 v t) =
      (q D Sc cutoff j.1 v t).comp (offDiagonalInputDotAffine D Sc cutoff j v t) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change actualSourceInputDot D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (shortTensor D Sc cutoff j.1 v s.word t g b)) = _
  rw [q_shortTensor, actualSourceInputDot_tensor, oldAppendDotComponent_eq]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j.1])).mkQ_surjective b
  rw [offDiagonalInputDotAffine_representative, map_smul, q_shortTensor]
  simp [j.property, SKM.zsign, oldComp_mk]

private theorem shortCross_decode_residual' (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) =
      z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) := by
  have hz := appendC0_residual_mem D Sc cutoff i v t z
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, hy⟩ := hz
  have hd := congrArg (ShortCrossCoordinates.decode D Sc cutoff i v t) hy
  simp only [ShortCrossCoordinates.decode_shortCross, map_sub,
    ShortCrossCoordinates.decode_embedding, sub_zero] at hd
  rw [hd] at hy
  exact hy

theorem actualSourceInputContraction_q_decode (j : {j : I // D.parity j = 1})
    (v t : List I) (z : AppendTarget D Sc cutoff j.1 v (t ++ [j.1])) :
    actualSourceInputContraction D Sc cutoff j v t
      (q D Sc cutoff j.1 v t (ShortCrossCoordinates.decode D Sc cutoff j.1 v t z)) =
      appendC0InputDefect D Sc cutoff j.1 v t z 0 := by
  rw [actualSourceInputContraction_q]
  change appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t (ShortCrossCoordinates.decode D Sc cutoff j.1 v t z)) 0 = _
  rw [shortCross_decode_residual', map_sub, appendC0InputDefect_embedding,
    sub_zero]

def offDiagonalBoundaryLift (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff j.1 v (t ++ [j.1]) :=
  (pMap D Sc cutoff j.1 v (t ++ [j.1])).comp
    (offDiagonalLongSection D Sc cutoff p j.1 v t)

theorem offDiagonalBoundaryLift_rho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalBoundaryLift D Sc cutoff p j v t
      (offDiagonalCoefficientRho D Sc cutoff p j v t f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (offDiagonalBoundaryLift D Sc cutoff p j v t f) := by
  change pMap D Sc cutoff j.1 v (t ++ [j.1])
    (offDiagonalLongSection D Sc cutoff p j.1 v t _) = _
  rw [← boundaryRho_offDiagonalLongSection, pMap_boundaryRho]
  rfl

/-- Actual source values of the decoded, uncorrected long lift. -/
def offDiagonalBoundaryCoordinates (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Source D Sc cutoff j.1 v t :=
  q D Sc cutoff j.1 v t ∘ₗ ShortCrossCoordinates.decode D Sc cutoff j.1 v t ∘ₗ
    offDiagonalBoundaryLift D Sc cutoff p j v t

theorem actualSourceInputDot_boundaryCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    actualSourceInputDot D Sc cutoff j v t (offDiagonalBoundaryCoordinates D Sc cutoff p j v t f) =
      offDiagonalBoundaryCoordinates D Sc cutoff p j v t
        (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  change actualSourceInputDot D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (ShortCrossCoordinates.decode D Sc cutoff j.1 v t
      (offDiagonalBoundaryLift D Sc cutoff p j v t f))) = _
  rw [actualSourceInputDot_q]
  change q D Sc cutoff j.1 v t
    (ShortCrossCoordinates.decode D Sc cutoff j.1 v t
      (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v t
          (ShortCrossCoordinates.decode D Sc cutoff j.1 v t
            (offDiagonalBoundaryLift D Sc cutoff p j v t f))))) = _
  rw [shortCross_decode_residual', map_sub, appendMovingPowerTarget_embedding_one,
    map_sub, ShortCrossCoordinates.decode_embedding, sub_zero, ← offDiagonalBoundaryLift_rho]
  rfl

private theorem inputShift_zero (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) : appendInputShift D Sc cutoff i v t f 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single m b => simp [appendInputShift, appendOutputShift]

theorem actualSourceInputContraction_boundaryCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    actualSourceInputContraction D Sc cutoff j v t
      (offDiagonalBoundaryCoordinates D Sc cutoff p j v t f) =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalCoefficientRho D Sc cutoff p j v t f) 0 := by
  rw [offDiagonalBoundaryCoordinates, LinearMap.comp_apply, LinearMap.comp_apply,
    actualSourceInputContraction_q_decode]
  change (appendC0 D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (offDiagonalBoundaryLift D Sc cutoff p j v t f)) -
      appendInputShift D Sc cutoff j.1 v t
        (appendC0 D Sc cutoff j.1 v t (offDiagonalBoundaryLift D Sc cutoff p j v t f))) 0 = _
  rw [Finsupp.sub_apply, inputShift_zero, sub_zero, ← offDiagonalBoundaryLift_rho]
  rfl

theorem actualSourceInputDot_iterate_boundaryCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    (actualSourceInputDot D Sc cutoff j v t)^[r]
      (offDiagonalBoundaryCoordinates D Sc cutoff p j v t f) =
      offDiagonalBoundaryCoordinates D Sc cutoff p j v t
        ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      actualSourceInputDot_boundaryCoordinates, Function.iterate_succ_apply']

theorem actualSourceInputContraction_corrected_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t) :
    actualSourceInputContraction D Sc cutoff j v t
      ((actualSourceInputDot D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalLongExtraction D Sc cutoff p j.1 v t
          (offDiagonalCorrectedLift D Sc cutoff p j v t (r + d + 1) b)) 0 := by
  rw [actualSourceInputDot_iterate_boundaryCoordinates,
    actualSourceInputContraction_boundaryCoordinates]
  simp only [offDiagonalLongExtraction_correctedLift]
  rw [← Function.iterate_add_apply]
  have hs : (offDiagonalCoefficientRho D Sc cutoff p j v t)^[r + d + 1] (Finsupp.single 0 b) =
      offDiagonalCoefficientRho D Sc cutoff p j v t
        ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[r + d] (Finsupp.single 0 b)) :=
    Function.iterate_succ_apply' _ _ _
  rw [hs]

theorem actualSourceInputContraction_corrected_below (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t)
    (h : r + d + 1 + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) :
    actualSourceInputContraction D Sc cutoff j v t
      ((actualSourceInputDot D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) = 0 := by
  rw [actualSourceInputContraction_corrected_iterate]
  exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t (r + d + 1) 0 b (by omega)

theorem actualSourceInputContraction_corrected_pivot (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t)
    (h : outputSDegree D j.1 v = r + d + 1 + endpointQPDegree D cutoff j.1 v) :
    actualSourceInputContraction D Sc cutoff j v t
      ((actualSourceInputDot D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) =
      offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t 0 b := by
  rw [actualSourceInputContraction_corrected_iterate]
  exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t (r + d + 1) 0 b (by omega)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

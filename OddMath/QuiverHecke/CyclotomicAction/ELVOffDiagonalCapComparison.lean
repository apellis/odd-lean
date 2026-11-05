import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapInput
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputMatrix

/-! # Comparison of categorical cap data with the input matrix

The fixed adjunction counit and induction dot, with the prescribed source
grading, agree with the descended input operators of DeformedMatrixComparison,
section 3, on arbitrary old Hom endpoints. This transfers the input inverse
of DeformedRouquierMatrix, section 4, without another matrix-elimination proof.
The unshifted source and row sign/twist normalization remain separate.
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

  change ((BalancedInduction.induction (append D Sc cutoff j.1)).map
    (movingCoefficientBackward D Sc cutoff j v)).total
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) = _
  change (BalancedInduction.moduleMap (append D Sc cutoff j.1)
    (movingCoefficientBackward D Sc cutoff j v)).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [movingCoefficientBackward_app, ↓reduceIte, one_ne_zero]
  change BalancedInduction.tensor (append D Sc cutoff j.1)
      (coefficient D Sc cutoff (D.parity j.1) j.1 v)
      (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff j.1)
      (coefficient D Sc cutoff (D.parity j.1) j.1 v)
      (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g)
      (0 : Old D Sc cutoff v (s ++ [j.1])) = _
  rw [BalancedInduction.tensor_zero_right, add_zero]
  rfl

theorem sourceInputContraction_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    sourceInputContraction D Sc cutoff j v t (tensor D Sc cutoff j.1 v s t g b) =
      oldComp D Sc cutoff v (s ++ [j.1]) t
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) g := by
  rw [← coefficientOneSourceEquiv_tensor, sourceInputContraction_carrier,
    shiftedInputContraction_tensor]

theorem sourceInputDot_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    sourceInputDot D Sc cutoff j v t (tensor D Sc cutoff j.1 v s t g b) =
      -tensor D Sc cutoff j.1 v s t
        (oldAppendDotComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g)
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) := by
  rw [← coefficientOneSourceEquiv_tensor, sourceInputDot_carrier,
    shiftedInputDot_tensor, map_neg, coefficientOneSourceEquiv_tensor]

theorem sourceInputContraction_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    sourceInputContraction D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      offDiagonalInputContractionAffine D Sc cutoff j v t z := by
  suffices h : (sourceInputContraction D Sc cutoff j v t).comp
      (q D Sc cutoff j.1 v t) = offDiagonalInputContractionAffine D Sc cutoff j v t from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply]
  change sourceInputContraction D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (shortTensor D Sc cutoff j.1 v s.word t g b)) = _
  rw [q_shortTensor, sourceInputContraction_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j.1])).mkQ_surjective b
  change _ = appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t
      (shortTensor D Sc cutoff j.1 v s.word t g ((ideal D Sc cutoff _ _).mkQ r))) 0
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same]
  change (ideal D Sc cutoff v t).mkQ (twist k 1 r ≫ g) = _
  simp [j.property, SKM.zsign]

theorem sourceInputDot_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    sourceInputDot D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t (offDiagonalCrossingInputDotAffine D Sc cutoff j v t z) := by
  suffices h : (sourceInputDot D Sc cutoff j v t).comp
      (q D Sc cutoff j.1 v t) =
      (q D Sc cutoff j.1 v t).comp (offDiagonalCrossingInputDotAffine D Sc cutoff j v t) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change sourceInputDot D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (shortTensor D Sc cutoff j.1 v s.word t g b)) =
    q D Sc cutoff j.1 v t
      (offDiagonalCrossingInputDotAffine D Sc cutoff j v t
        (shortTensor D Sc cutoff j.1 v s.word t g b))
  rw [q_shortTensor, sourceInputDot_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j.1])).mkQ_surjective b
  have hx := offDiagonalCrossingInputDotAffine_representative
    D Sc cutoff j v s.word t r g
  have hq := congrArg (q D Sc cutoff j.1 v t) hx
  rw [map_smul, q_shortTensor] at hq
  rw [hq, oldAppendDotComponent_eq]
  change -tensor D Sc cutoff j.1 v s.word t
      ((ideal D Sc cutoff (s.word ++ [j.1]) t).mkQ
        (appendMovingPower D Sc cutoff j.1 s.word 1 ≫ g))
      ((ideal D Sc cutoff v (s.word ++ [j.1])).mkQ (twist k 1 r)) =
    SKM.zsign k (D.parity j.1 * D.parity j.1) •
      tensor D Sc cutoff j.1 v s.word t
        ((ideal D Sc cutoff (s.word ++ [j.1]) t).mkQ
          (appendMovingPower D Sc cutoff j.1 s.word 1 ≫ g))
        ((ideal D Sc cutoff v (s.word ++ [j.1])).mkQ (twist k (D.parity j.1) r))
  simp [j.property, SKM.zsign]


/-- Equality with the specified input contraction, proved on all balanced classes. -/
theorem sourceInputContraction_eq (j : {j : I // D.parity j = 1}) (v t : List I) :
    sourceInputContraction D Sc cutoff j v t =
      offDiagonalInputContraction D Sc cutoff j v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
  rw [sourceInputContraction_q, offDiagonalInputContraction_q]

/-- Equality with the specified input dot, retaining the whole coefficient twist. -/
theorem sourceInputDot_eq (j : {j : I // D.parity j = 1}) (v t : List I) :
    sourceInputDot D Sc cutoff j v t =
      offDiagonalCrossingInputDot D Sc cutoff j v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
  rw [sourceInputDot_q, offDiagonalCrossingInputDot_q]

/-- The crossing and rows from the constructed shifted counit and source dot. -/
def offDiagonalShiftedInputMatrix (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) :
    Source D Sc cutoff j.1 v t →ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  (toCyclotomic D Sc cutoff j.1 v t).prod
    (LinearMap.pi fun r : Fin m =>
      (sourceInputContraction D Sc cutoff j v t).comp
        ((sourceInputDot D Sc cutoff j v t) ^ r.val))

theorem offDiagonalShiftedInputMatrix_eq (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ) :
    offDiagonalShiftedInputMatrix D Sc cutoff j v t m =
      offDiagonalInputMatrix D Sc cutoff j v t m := by
  simp only [offDiagonalShiftedInputMatrix, sourceInputContraction_eq, sourceInputDot_eq,
    offDiagonalInputMatrix, offDiagonalInputCapVector]

/-- Transfer of the concrete inverse to the constructed shifted categorical maps. -/
def offDiagonalShiftedInputMatrixEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Source D Sc cutoff j.1 v t ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  LinearEquiv.ofBijective (offDiagonalShiftedInputMatrix D Sc cutoff j v t m) (by
    rw [offDiagonalShiftedInputMatrix_eq]
    exact offDiagonalInputMatrix_bijective D Sc cutoff p j v t m hm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

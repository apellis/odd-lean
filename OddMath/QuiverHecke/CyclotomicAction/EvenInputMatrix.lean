import OddMath.QuiverHecke.CyclotomicAction.EvenBoundaryRecurrence
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.Algebra.FiniteTriangularCoordinates
import OddMath.Algebra.LowPolynomialCoordinates
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalInput
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import Mathlib.LinearAlgebra.Pi
import OddMath.Algebra.FiniteSuperspace

/-!
# Even input matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Even counit and induction-dot input comparison
The canonical even source and ordinary adjunction counit/dot in
DeformedMatrixComparison §4 agree with the prescribed raw input operators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The induction dot on the literal even-moving coefficient module. -/
def evenSourceInputDot (i : {i : I // D.parity i = 0}) (v t : List I) :
    Source D Sc cutoff i.1 v t →ₗ[k] Source D Sc cutoff i.1 v t :=
  inductionDot D Sc cutoff i.1 (evenMovingCoefficientModule D Sc cutoff i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

theorem evenSourceInputDot_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    evenSourceInputDot D Sc cutoff i v t (tensor D Sc cutoff i.1 v s t g b) =
      tensor D Sc cutoff i.1 v s t
        (oldAppendDotComponent D Sc cutoff i.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g) b := by
  change inductionDot D Sc cutoff i.1 (evenMovingCoefficientModule D Sc cutoff i v) _
    (BalancedInduction.tensor _ _ _ g b) = _
  rw [inductionDot_tensor]
  have hg : twist k (D.parity i.1)
      (X := (append D Sc cutoff i.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g = g := by
    rw [i.property, twist_zero]
  rw [hg]
  rfl

theorem evenSourceInputContraction_q (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ShortTarget D Sc cutoff i.1 v t) :
    evenSourceInputContraction D Sc cutoff i v t (q D Sc cutoff i.1 v t z) =
      evenInputContractionAffine D Sc cutoff i.1 v t z := by
  suffices h : (evenSourceInputContraction D Sc cutoff i v t).comp
      (q D Sc cutoff i.1 v t) = evenInputContractionAffine D Sc cutoff i.1 v t from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputContraction D Sc cutoff i v t
    (q D Sc cutoff i.1 v t (shortTensor D Sc cutoff i.1 v s.word t g b)) = _
  rw [q_shortTensor, evenSourceInputContraction_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i.1])).mkQ_surjective b
  change _ = appendC0InputDefect D Sc cutoff i.1 v t
    (shortCross D Sc cutoff i.1 v t
      (shortTensor D Sc cutoff i.1 v s.word t g ((ideal D Sc cutoff _ _).mkQ r))) 0
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.neg_apply, Finsupp.single_eq_same, i.property, zero_mul,
    SKM.zsign_zero, twist_zero, neg_one_smul]
  rfl

theorem evenSourceInputDot_q (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ShortTarget D Sc cutoff i.1 v t) :
    evenSourceInputDot D Sc cutoff i v t (q D Sc cutoff i.1 v t z) =
      q D Sc cutoff i.1 v t (evenCrossingInputDotAffine D Sc cutoff i.1 v t z) := by
  suffices h : (evenSourceInputDot D Sc cutoff i v t).comp (q D Sc cutoff i.1 v t) =
      (q D Sc cutoff i.1 v t).comp (evenCrossingInputDotAffine D Sc cutoff i.1 v t) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputDot D Sc cutoff i v t
    (q D Sc cutoff i.1 v t (shortTensor D Sc cutoff i.1 v s.word t g b)) =
    q D Sc cutoff i.1 v t
      (evenCrossingInputDotAffine D Sc cutoff i.1 v t
        (shortTensor D Sc cutoff i.1 v s.word t g b))
  rw [q_shortTensor, evenSourceInputDot_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i.1])).mkQ_surjective b
  rw [evenCrossingInputDotAffine_representative D Sc cutoff i.1 i.property,
    q_shortTensor, oldAppendDotComponent_eq]
  rfl

/-- Equality on all balanced classes, not only on chosen representatives. -/
theorem evenSourceInputContraction_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenSourceInputContraction D Sc cutoff i v t =
      evenInputContraction D Sc cutoff i.1 i.property v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i.1 v t z
  rw [evenSourceInputContraction_q, evenInputContraction_q]

/-- The ordinary actual induction dot is the prescribed even input dot. -/
theorem evenSourceInputDot_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenSourceInputDot D Sc cutoff i v t =
      evenCrossingInputDot D Sc cutoff i.1 i.property v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i.1 v t z
  rw [evenSourceInputDot_q, evenCrossingInputDot_q]

/-- The canonical source comparison intertwines the ordinary actual dot.
There is no parity conjugation or higher-row scalar for an even colour. -/
theorem evenSourceInputDot_sourceEquiv (i : {i : I // D.parity i = 0})
    (v t : List I)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    evenSourceInputDot D Sc cutoff i v t (evenSourceEquiv D Sc cutoff i v t z) =
      evenSourceEquiv D Sc cutoff i v t
        (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  suffices h : (evenSourceInputDot D Sc cutoff i v t).comp
      (evenSourceEquiv D Sc cutoff i v t).toLinearMap =
      (evenSourceEquiv D Sc cutoff i v t).toLinearMap.comp
        (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff)) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputDot D Sc cutoff i v t
    (evenSourceEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i.1)
        (restrictedRepresentable D Sc cutoff i.1 v).toFunctor s g b)) =
    evenSourceEquiv D Sc cutoff i v t
      (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v) _
        (BalancedInduction.tensor _ _ s g b))
  rw [evenSourceEquiv_tensor, evenSourceInputDot_tensor, inductionDot_tensor]
  have hg : twist k (D.parity i.1)
      (X := (append D Sc cutoff i.1).obj s)
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g = g := by
    rw [i.property, twist_zero]
  rw [hg, evenSourceEquiv_tensor]

theorem evenSourceInputDot_iterate_sourceEquiv (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    (evenSourceInputDot D Sc cutoff i v t)^[n] (evenSourceEquiv D Sc cutoff i v t z) =
      evenSourceEquiv D Sc cutoff i v t ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, evenSourceInputDot_sourceEquiv,
      Function.iterate_succ_apply']

/-- Every even cap row has the same constant minus relative to the ordinary
adjunction counit, independently of the row index. -/
theorem evenCapRow_normalization (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    evenSourceInputContraction D Sc cutoff i v t
      ((evenSourceInputDot D Sc cutoff i v t)^[n] (evenSourceEquiv D Sc cutoff i v t z)) =
      -unshiftedCounitComponent D Sc cutoff i.1 v t ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  rw [evenSourceInputDot_iterate_sourceEquiv, evenSourceInputContraction_counit]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Cap pivots on even boundary lifts

The parity-zero input pivots in DeformedRouquierMatrix, section 4.
Decoded moving dots shift the ordinary long coordinates. The raw cap reads
the constant coefficient of the next boundary row. The actual arbitrary-Hom
leading theorem therefore gives the anti-diagonal unit and below-diagonal
vanishing, with every old coefficient and balance twist retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The even negative-height input matrix

DeformedRouquierMatrix, section 4: the prescribed even crossing and its
actual descended raw input cap rows form an invertible augmented map.
The ordinary low polynomial coefficients identify the crossing kernel;
its cap matrix has the proved anti-triangular unit pivots on every old Hom.
The categorical coefficient(0) counit comparison remains separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
open OddMath.LowPolynomialCoordinates
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The raw cap vector uses the actual descended contraction and input dot. -/
def evenInputCapVector (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ) :
    Source D Sc cutoff i v t →ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  LinearMap.pi fun r : Fin m =>
    (evenInputContraction D Sc cutoff i hi v t).comp ((evenCrossingInputDot D Sc cutoff i hi v t) ^ r.val)

@[simp] theorem evenInputCapVector_apply (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ) (s : Source D Sc cutoff i v t) (r : Fin m) :
    evenInputCapVector D Sc cutoff i hi v t m s r =
      evenInputContraction D Sc cutoff i hi v t ((evenCrossingInputDot D Sc cutoff i hi v t)^[r.val] s) := by
  exact congrArg (evenInputContraction D Sc cutoff i hi v t)
    (Module.End.pow_apply (evenCrossingInputDot D Sc cutoff i hi v t) r.val s)

private def kernelWindowVectorEquiv (i : I)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] evenBoundaryKernelWindow D Sc cutoff i v t where
  toFun f := ⟨(lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m f).val, by
    intro d hd
    have hlt : d < m := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m f).property hd
    change d + endpointQPDegree D cutoff i v < outputSDegree D i v
    omega⟩
  invFun f := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).symm ⟨f.val, by
    intro d hd
    have hlt := f.property hd
    change d + endpointQPDegree D cutoff i v < outputSDegree D i v at hlt
    change d < m
    omega⟩
  left_inv f := by
    apply (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).injective
    rw [LinearEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v t)) ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).apply_symm_apply _)
  map_add' f g := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v t)) (map_add (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m) f g)
  map_smul' c f := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v t)) (map_smul (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m) c f)

/-- Coordinates in the even boundary kernel, using the ordinary low window. -/
def evenBoundaryKernelVectorEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  (kernelWindowVectorEquiv D Sc cutoff i v t m hm).trans
    (evenBoundaryKernelEquiv D Sc cutoff p i hi v t)

theorem evenBoundaryKernelVectorEquiv_single (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m)
    (d : Fin m) (b : Old D Sc cutoff v t) :
    ((evenBoundaryKernelVectorEquiv D Sc cutoff p i hi v t m hm (Pi.single d b)) :
      ℕ →₀ Old D Sc cutoff v t) =
      Finsupp.single d.val b := by
  change ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m (Pi.single d b)).val) = _
  exact lowVectorEquiv_single m d b

def evenCrossingKernelVectorEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff i v t) :=
  (evenBoundaryKernelVectorEquiv D Sc cutoff p i hi v t m hm).trans
    (offDiagonalBoundarySnakeKernelEquiv D Sc cutoff p i v t)

/-- The actual boundary snake equals the decoded original long lift in the quotient. -/
theorem evenBoundarySnake_eq_boundaryCrossCoordinates (p : ZMod 2)
    (i : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p i v t)) :
    offDiagonalBoundarySnake D Sc cutoff p i v t f =
      q D Sc cutoff i v t (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) := by
  exact offDiagonalBoundarySnake_eq_lift D Sc cutoff p i v t f
    (offDiagonalLongSection D Sc cutoff p i v t f)
    (offDiagonalLongExtraction_section D Sc cutoff p i v t f)

/-- The actual cap vector evaluated on the actual snake kernel coordinates. -/
def evenCapOnKernelVector (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) →ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  (evenInputCapVector D Sc cutoff i hi v t m).comp
    ((LinearMap.ker (toCyclotomic D Sc cutoff i v t)).subtype.comp
      (evenCrossingKernelVectorEquiv D Sc cutoff p i hi v t m hm).toLinearMap)

theorem evenCapOnKernelVector_single (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m)
    (r d : Fin m) (b : Old D Sc cutoff v t) :
    evenCapOnKernelVector D Sc cutoff p i hi v t m hm (Pi.single d b) r =
      evenInputContractionAffine D Sc cutoff i v t
        ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r.val]
          (evenBoundaryCrossCoordinates D Sc cutoff p i v t
            (Finsupp.single d.val b))) := by
  change evenInputCapVector D Sc cutoff i hi v t m
    ((evenCrossingKernelVectorEquiv D Sc cutoff p i hi v t m hm (Pi.single d b)).val) r = _
  rw [evenInputCapVector_apply]
  change evenInputContraction D Sc cutoff i hi v t
    ((evenCrossingInputDot D Sc cutoff i hi v t)^[r.val]
      (offDiagonalBoundarySnake D Sc cutoff p i v t
        (evenBoundaryKernelVectorEquiv D Sc cutoff p i hi v t m hm (Pi.single d b)))) = _
  rw [evenBoundarySnake_eq_boundaryCrossCoordinates, evenInputContraction_iterate_q,
    evenBoundaryKernelVectorEquiv_single]

theorem evenCapOnKernelVector_bijective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Function.Bijective (evenCapOnKernelVector D Sc cutoff p i hi v t m hm) := by
  classical
  let R := reversedVector (k := k) (M := Old D Sc cutoff v t) m
  let F := evenCapOnKernelVector D Sc cutoff p i hi v t m hm
  have ht : Function.Bijective (F.comp R.toLinearMap) := by
    apply OddMath.FiniteTriangularCoordinates.bijective m _ (evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    · intro a b hab x
      change F (R (Pi.single b x)) a = 0
      rw [reversedVector_single, evenCapOnKernelVector_single]
      apply evenInputContractionAffine_below D Sc cutoff p i hi v t
      have hb : b.rev.val = m - (b.val + 1) := rfl
      have ha := a.isLt
      have hb' := b.isLt
      have hab' : a.val < b.val := hab
      omega
    · intro a x
      change F (R (Pi.single a x)) a = _
      rw [reversedVector_single, evenCapOnKernelVector_single]
      apply evenInputContractionAffine_pivot D Sc cutoff p i hi v t
      have ha : a.rev.val = m - (a.val + 1) := rfl
      have ha' := a.isLt
      omega
  constructor
  · intro f g hfg
    have he : R.symm f = R.symm g := by
      apply ht.1
      change F (R (R.symm f)) = F (R (R.symm g))
      simpa only [LinearEquiv.apply_symm_apply] using hfg
    exact R.symm.injective he
  · intro f
    obtain ⟨g, hg⟩ := ht.2 f
    exact ⟨R g, hg⟩

/-- Cap rows detect exactly the kernel of the prescribed crossing. -/
theorem evenInputCapVector_kernel_bijective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Function.Bijective ((evenInputCapVector D Sc cutoff i hi v t m).comp
      (LinearMap.ker (toCyclotomic D Sc cutoff i v t)).subtype) := by
  let e := evenCrossingKernelVectorEquiv D Sc cutoff p i hi v t m hm
  have hb := evenCapOnKernelVector_bijective D Sc cutoff p i hi v t m hm
  constructor
  · intro f g hfg
    change evenInputCapVector D Sc cutoff i hi v t m f.val = evenInputCapVector D Sc cutoff i hi v t m g.val at hfg
    have he : e.symm f = e.symm g := by
      apply hb.1
      change evenInputCapVector D Sc cutoff i hi v t m (e (e.symm f)).val =
        evenInputCapVector D Sc cutoff i hi v t m (e (e.symm g)).val
      simpa only [LinearEquiv.apply_symm_apply] using hfg
    exact e.symm.injective he
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    exact ⟨e g, hg⟩

/-- The negative branch uses the prescribed crossing and actual dotted input contractions. -/
def evenInputMatrix (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ) :
    Source D Sc cutoff i v t →ₗ[k]
      (Old D Sc cutoff (v ++ [i]) (t ++ [i]) × (Fin m → Old D Sc cutoff v t)) :=
  (toCyclotomic D Sc cutoff i v t).prod (evenInputCapVector D Sc cutoff i hi v t m)

theorem evenInputMatrix_bijective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Function.Bijective (evenInputMatrix D Sc cutoff i hi v t m) := by
  have hb := evenInputCapVector_kernel_bijective D Sc cutoff p i hi v t m hm
  constructor
  · intro f g hfg
    have hcross := congrArg Prod.fst hfg
    have hcap := congrArg Prod.snd hfg
    change toCyclotomic D Sc cutoff i v t f = toCyclotomic D Sc cutoff i v t g at hcross
    change evenInputCapVector D Sc cutoff i hi v t m f = evenInputCapVector D Sc cutoff i hi v t m g at hcap
    let d : LinearMap.ker (toCyclotomic D Sc cutoff i v t) :=
      ⟨f - g, by
        change toCyclotomic D Sc cutoff i v t (f - g) = 0
        have hs : toCyclotomic D Sc cutoff i v t (f - g) =
            toCyclotomic D Sc cutoff i v t f - toCyclotomic D Sc cutoff i v t g :=
          map_sub (toCyclotomic D Sc cutoff i v t) f g
        exact hs.trans (sub_eq_zero.mpr hcross)⟩
    have hd : d = 0 := hb.1 (by
      change evenInputCapVector D Sc cutoff i hi v t m (f - g) =
        evenInputCapVector D Sc cutoff i hi v t m (0 : Source D Sc cutoff i v t)
      have hs : evenInputCapVector D Sc cutoff i hi v t m (f - g) =
          evenInputCapVector D Sc cutoff i hi v t m f - evenInputCapVector D Sc cutoff i hi v t m g :=
        map_sub (evenInputCapVector D Sc cutoff i hi v t m) f g
      exact hs.trans ((sub_eq_zero.mpr hcap).trans
        (evenInputCapVector D Sc cutoff i hi v t m).map_zero.symm))
    exact sub_eq_zero.mp (congrArg Subtype.val hd)
  · rintro ⟨n, b⟩
    obtain ⟨z, hz⟩ := evenToCyclotomic_surjective_of_nonpositive_height
      D Sc cutoff p i hi v t (by omega) n
    obtain ⟨f, hf⟩ := hb.2 (b - evenInputCapVector D Sc cutoff i hi v t m z)
    refine ⟨z + f.val, ?_⟩
    apply Prod.ext
    · change toCyclotomic D Sc cutoff i v t (z + f.val) = n
      have hfk := f.property
      change toCyclotomic D Sc cutoff i v t f.val = 0 at hfk
      rw [map_add, hz, hfk, add_zero]
    · change evenInputCapVector D Sc cutoff i hi v t m (z + f.val) = b
      rw [map_add]
      change evenInputCapVector D Sc cutoff i hi v t m z +
        ((evenInputCapVector D Sc cutoff i hi v t m).comp
          (LinearMap.ker (toCyclotomic D Sc cutoff i v t)).subtype) f = b
      rw [hf]
      abel

/-- The whole raw negative-height augmented matrix on the independently defined source. -/
def evenInputMatrixEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Source D Sc cutoff i v t ≃ₗ[k]
      (Old D Sc cutoff (v ++ [i]) (t ++ [i]) × (Fin m → Old D Sc cutoff v t)) :=
  LinearEquiv.ofBijective (evenInputMatrix D Sc cutoff i hi v t m)
    (evenInputMatrix_bijective D Sc cutoff p i hi v t m hm)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Even ordinary dotted-counit inverse
DeformedMatrixComparison §4 transports the even negative-height raw matrix
to the canonical ordinary Ind–Res source and ordinary dotted counit rows.
The first row remains explicitly minus crossing after J; its ordered mate
identification is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenCounitMatrixEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      (Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) × (Fin m → Old D Sc cutoff v t)) :=
  ((evenSourceEquiv D Sc cutoff i v t).trans
    (evenInputMatrixEquiv D Sc cutoff p i.1 i.property v t m hm)).trans
      (LinearEquiv.neg k)

@[simp] theorem evenCounitMatrixEquiv_fst (p : ZMod 2)
    (i : {i : I // D.parity i = 0}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    (evenCounitMatrixEquiv D Sc cutoff p i v t m hm z).1 =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := rfl

/-- All remaining rows are the ordinary counit followed by ordinary dot powers. -/
theorem evenCounitMatrixEquiv_cap (p : ZMod 2)
    (i : {i : I // D.parity i = 0}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) (r : Fin m) :
    (evenCounitMatrixEquiv D Sc cutoff p i v t m hm z).2 r =
      unshiftedCounitComponent D Sc cutoff i.1 v t
        ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  change -evenInputContraction D Sc cutoff i.1 i.property v t
    (((evenCrossingInputDot D Sc cutoff i.1 i.property v t) ^ r.val)
      (evenSourceEquiv D Sc cutoff i v t z)) = _
  rw [← evenSourceInputContraction_eq, ← evenSourceInputDot_eq, Module.End.pow_apply,
    evenCapRow_normalization, neg_neg]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Even shifted cap-family component inverse
DeformedMatrixComparison section 4 has the same canonical cap target
family for the even-moving case, with ordinary unscaled dotted counits.
Only representable component inversion is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Even negative-height inverse on the literal finite shifted cap target. -/
def evenCapFamilyComponentEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :=
  (evenCounitMatrixEquiv D Sc cutoff p i v t m hm).trans
    (capFamilyComponentCoordinates D Sc cutoff i.1 v t m).symm

/-- The canonical coordinates give the actual ordinary even counit matrix. -/
theorem evenCapFamilyComponentEquiv_coordinates (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z) =
      evenCounitMatrixEquiv D Sc cutoff p i v t m hm z := by
  exact (capFamilyComponentCoordinates D Sc cutoff i.1 v t m).apply_symm_apply _

/-- The first canonical coordinate remains the specified signed crossing. -/
theorem evenCapFamilyComponentEquiv_fst (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    (capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z)).1 =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  rw [evenCapFamilyComponentEquiv_coordinates, evenCounitMatrixEquiv_fst]

/-- Each remaining canonical coordinate is the ordinary dotted counit. -/
theorem evenCapFamilyComponentEquiv_cap (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) (r : Fin m) :
    (capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z)).2 r =
      unshiftedCounitComponent D Sc cutoff i.1 v t
        ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  rw [evenCapFamilyComponentEquiv_coordinates]
  exact evenCounitMatrixEquiv_cap D Sc cutoff p i v t m hm z r

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The actual even mate is the canonical first crossing row

The coefficient(0) source comparison has no parity shift or tensor twist.
The fixed signed mate evaluates to minus toCyclotomic after this actual J0.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenModuleMate_firstRow_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i.1).app 0
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -toCyclotomic D Sc cutoff i.1 v t
      (evenSourceEquiv D Sc cutoff i v t
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) := by
  have hp : D.parity i.1 * D.parity i.1 = 0 := by rw [i.property]; decide
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff i.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) hp.symm
  have hJ := evenSourceEquiv_tensor D Sc cutoff i v s t g b
  dsimp only [restrictedRepresentable] at hJ
  rw [hJ, hc, oldModuleMate_upper_tensor D Sc cutoff i.1 v s t g b,
    toCyclotomic_tensor D Sc cutoff i.1 v s t g b,
    pairing_eq_append_comp D Sc cutoff i.1 v s t g b, hp, twist_zero]

theorem evenModuleMate_firstRow (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i.1).app 0
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  exact coend_total_ext (append D Sc cutoff i.1)
    ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff i.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
    ((oldModuleMate D Sc cutoff i.1).app 0
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
    (OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap
    (toCyclotomic D Sc cutoff i.1 v t)
    (evenSourceEquiv D Sc cutoff i v t).toLinearMap
    (fun s g b => by
      cases s with
      | mk s => exact evenModuleMate_firstRow_tensor D Sc cutoff i v s t g b) z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The actual mate in shifted finite matrix component inverses
DeformedMatrixComparison section 4 identifies the inverted first
coordinate with the fixed ordered categorical mate. The unit columns
remain the ordinary unscaled columns, with canonical source coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The typed actual mate component has exactly the inverted first-row normalization. -/
theorem matrixMateComponent_firstRow (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      ((matrixMateComponent D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff) z) =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff j.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) j.property
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((oldModuleMate D Sc cutoff j.1).app (D.parity j.1)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) = _
  rw [hc]
  exact oldModuleMate_firstRow D Sc cutoff j v t z

/-- The actual mate as a linear row with literal Old quotient coordinates. -/
def matrixMateRow (i : I) (v t : List I) :
    (unshiftedSourceModule D Sc cutoff i v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap.comp
      (SVec.toLinearMap ((matrixMateComponent D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)))

theorem matrixMateRow_apply (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff j.1 v t z =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  exact matrixMateComponent_firstRow D Sc cutoff j v t z

/-- The positive component inverse has the actual ordered mate and unscaled ordinary unit columns. -/
theorem unitFamilyComponentEquiv_eq (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    unitFamilyComponentEquiv D Sc cutoff p j v t m hm x =
      matrixMateRow D Sc cutoff j.1 v t
        (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).1 +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff j.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2 r) := by
  rw [matrixMateRow_apply, unitFamilyComponentEquiv_apply]

/-- The negative component inverse has the actual ordered mate and ordinary module cap rows. -/
theorem capFamilyComponentEquiv_eq (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z) =
      (matrixMateRow D Sc cutoff j.1 v t z,
        fun r : Fin m => (moduleCapRow D Sc cutoff j.1
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  apply Prod.ext
  · rw [capFamilyComponentEquiv_fst, matrixMateRow_apply]
  · funext r
    rw [capFamilyComponentEquiv_cap]
    have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩ r.val) z
    change (moduleCapRow D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff) z =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          (((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff)) ^ r.val) z) at h
    rw [Module.End.pow_apply] at h
    exact h.symm

/-- The even typed mate row has the canonical coefficient-zero source normalization. -/
theorem matrixMateRow_even_apply (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff i.1 v t z =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff i.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) i.property
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((oldModuleMate D Sc cutoff i.1).app (D.parity i.1)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) = _
  rw [hc]
  exact evenModuleMate_firstRow D Sc cutoff i v t z

/-- Even positive components use the fixed actual mate and unscaled ordinary unit columns. -/
theorem evenUnitFamilyComponentEquiv_eq (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm x =
      matrixMateRow D Sc cutoff i.1 v t
        (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1 +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2 r) := by
  rw [matrixMateRow_even_apply, evenUnitFamilyComponentEquiv_apply]

/-- Even negative components use the actual mate and ordinary unscaled module cap rows. -/
theorem evenCapFamilyComponentEquiv_eq (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z) =
      (matrixMateRow D Sc cutoff i.1 v t z,
        fun r : Fin m => (moduleCapRow D Sc cutoff i.1
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  apply Prod.ext
  · rw [evenCapFamilyComponentEquiv_fst, matrixMateRow_even_apply]
  · funext r
    rw [evenCapFamilyComponentEquiv_cap]
    have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩ r.val) z
    change (moduleCapRow D Sc cutoff i.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff) z =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff i.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          (((inductionDot D Sc cutoff i.1
            ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff)) ^ r.val) z) at h
    rw [Module.End.pow_apply] at h
    exact h.symm

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-right covariance of the actual normalized mate kernel

The right coefficient action is ordinary precomposition b ↦ a ≫ b for
every arrow a, including inhomogeneous arrows. The actual mate formula
keeps b untwisted. Its co-Yoneda component therefore defines a natural map
between the concrete IndRes and upper Hom coefficient presheaves.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def kernelNatTrans
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v)) : K ⟶ L where
  app v := ModuleCat.ofHom (f v)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact hf a

/-- The representable coefficient functors agree literally in the old category. -/
def oldSourceKernelEquiv (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t ≃ₗ[k]
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v))).obj t :=
  LinearEquiv.refl k _

@[simp] theorem oldSourceKernelEquiv_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    oldSourceKernelEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v)).toFunctor s g b := rfl

/-- Source comparison with the precise domain expected by the stored mate row. -/
def oldSourceKernelLinear (i : I) (v t : List I) :
    IndResKernel.Component (k := k) (append D Sc cutoff i)
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff) →ₗ[k]
      (unshiftedSourceModule D Sc cutoff i v).obj
        (⟨t⟩ : OldCategory D Sc cutoff) :=
  (oldSourceKernelEquiv D Sc cutoff i ⟨v⟩ ⟨t⟩).toLinearMap

theorem oldSourceKernelLinear_tensor (i : I) (v s t : List I)
    (g : (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff) ⟶
      (⟨t⟩ : OldCategory D Sc cutoff))
    (b : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ (append D Sc cutoff i).obj ⟨s⟩) :
    oldSourceKernelLinear D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) ⟨v⟩) ⟨s⟩ g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff ⟨v⟩)).toFunctor ⟨s⟩ g b :=
  oldSourceKernelEquiv_tensor D Sc cutoff i ⟨v⟩ ⟨s⟩ ⟨t⟩ g b

private theorem matrixMateRow_total (i : I) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff i v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff i v t z =
      OldInductionRepresentable.upperHomEquiv D Sc cutoff i
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
        ((matrixMateComponent D Sc cutoff i
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := rfl

/-- The chosen actual mate, evaluated in canonical upper-Hom coordinates. -/
def mateKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) := by
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      exact (matrixMateRow D Sc cutoff i v t).comp
        (oldSourceKernelLinear D Sc cutoff i v t)

/-- The stored row and its source linear map share the same module endpoint. -/
theorem mateKernelComponent_row (i : I) (v t : List I)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i)
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)) :
    mateKernelComponent D Sc cutoff i ⟨v⟩ ⟨t⟩ z =
      matrixMateRow D Sc cutoff i v t (oldSourceKernelLinear D Sc cutoff i v t z) := rfl

@[simp] theorem mateKernelComponent_tensor (i : I)
    (v s t : OldCategory D Sc cutoff) (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    mateKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
    -((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) := by
  cases v with
  | mk v =>
    cases s with
    | mk s =>
      cases t with
      | mk t =>
        rw [mateKernelComponent_row]
        rw [oldSourceKernelLinear_tensor, matrixMateRow_total]
        have hp : D.parity i * D.parity i = D.parity i := by
          rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
        have ht := oldModuleMate_upper_tensor D Sc cutoff i v s t g b
        rw [hp] at ht
        exact ht

theorem mateKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (mateKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k ((append D Sc cutoff i).obj t) ((append D Sc cutoff i).map a)).comp
      (mateKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor,
    mateKernelComponent_tensor]
  change -((append D Sc cutoff i).map (a ≫ b) ≫ equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) =
    (append D Sc cutoff i).map a ≫
      (-((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i) ((append D Sc cutoff i).map g)))
  rw [Functor.map_comp, Preadditive.comp_neg, Category.assoc]

/-- The same actual mate coefficient with literal kernel-object endpoints. -/
def mateKernelLinear (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v →ₗ[k]
      (BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t)).obj v :=
  mateKernelComponent D Sc cutoff i v.unop t

/-- The typed kernel-object coefficient is the fixed actual mate coefficient. -/
theorem mateKernelLinear_eq_component (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    mateKernelLinear D Sc cutoff i v t =
      mateKernelComponent D Sc cutoff i v.unop t := rfl

/-- The actual normalized first entry is ordinary-right natural, not merely even-arrow natural. -/
def mateKernel (i : I) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) :=
  kernelNatTrans _ _ (fun v => mateKernelLinear D Sc cutoff i v t)
    (fun a => mateKernelComponent_precompose D Sc cutoff i a.unop t)

@[simp] theorem mateKernel_apply (i : I) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    (mateKernel D Sc cutoff i t).app (op v) z =
      mateKernelComponent D Sc cutoff i v t z := by
  change mateKernelLinear D Sc cutoff i (op v) t z = _
  rw [mateKernelLinear_eq_component]
  simp only [Opposite.unop_op]
  exact LinearMap.congr_fun
    (rfl : mateKernelComponent D Sc cutoff i v t =
      mateKernelComponent D Sc cutoff i v t) z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-right covariance of the actual counit-dot rows

The source action is ordinary coefficient precomposition for all arrows.
The actual induction dot changes only the first tensor factor, and the
ordinary counit composes the untwisted coefficient with that factor.
Consequently every actual ordinary counit/dot-power row is right natural.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def transportEnd {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) : Module.End k V :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

private theorem transportEnd_apply {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) (x : V) :
    transportEnd e T x = e.symm (T (e x)) := rfl

private theorem transportEnd_pow_apply {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) (n : ℕ) (x : V) :
    e ((transportEnd e T ^ n) x) = (T ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, transportEnd_apply,
      e.apply_symm_apply, pow_succ, Module.End.mul_apply]

private theorem pow_intertwining {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (q : V →ₗ[k] W) (S : Module.End k V) (T : Module.End k W)
    (h : T.comp q = q.comp S) (n : ℕ) : (T ^ n).comp q = q.comp (S ^ n) := by
  have hs : Function.Semiconj q S T := fun x => (LinearMap.congr_fun h x).symm
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Module.End.pow_apply]
  exact (hs.iterate_right n x).symm

@[simp] theorem oldSourceKernelEquiv_symm_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    (oldSourceKernelEquiv D Sc cutoff i v t).symm
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v)).toFunctor s g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b := rfl

def dotKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    Module.End k (IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :=
  transportEnd (oldSourceKernelEquiv D Sc cutoff i v t)
    (inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff v)) t)

@[simp] theorem dotKernelComponent_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    dotKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s
      (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b := by
  rw [dotKernelComponent, transportEnd_apply, oldSourceKernelEquiv_tensor]
  have h := inductionDot_tensor D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff v)) s t g b
  exact (congrArg (oldSourceKernelEquiv D Sc cutoff i v t).symm h).trans
    (oldSourceKernelEquiv_symm_tensor D Sc cutoff i v s t
      (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b)

theorem dotKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (dotKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t).comp
      (dotKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor, dotKernelComponent_tensor]

def counitKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k] (v ⟶ t) :=
  (unshiftedCounitComponent D Sc cutoff i v.word t.word).comp
    (oldSourceKernelEquiv D Sc cutoff i v t).toLinearMap

theorem counitKernelComponent_apply (i : I) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    counitKernelComponent D Sc cutoff i v t z =
      unshiftedCounitComponent D Sc cutoff i v.word t.word
        (oldSourceKernelEquiv D Sc cutoff i v t z) := rfl

@[simp] theorem counitKernelComponent_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    counitKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) = b ≫ g := by
  rw [counitKernelComponent_apply, oldSourceKernelEquiv_tensor]
  cases v with
  | mk v =>
    cases s with
    | mk s =>
      cases t with
      | mk t => exact unshiftedCounitComponent_tensor D Sc cutoff i v s t g b

theorem counitKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (counitKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k t a).comp (counitKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor,
    counitKernelComponent_tensor]
  exact Category.assoc a b g

/-- Underlying coefficient component of the actual ordinary counit/dot-power row. -/
def capKernelComponent (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k] (v ⟶ t) :=
  (counitKernelComponent D Sc cutoff i v t).comp
    (dotKernelComponent D Sc cutoff i v t ^ n)

theorem capKernelComponent_precompose (i : I) (n : ℕ)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (capKernelComponent D Sc cutoff i n v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k t a).comp (capKernelComponent D Sc cutoff i n w t) := by
  have hd := pow_intertwining
    (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t)
    (dotKernelComponent D Sc cutoff i w t) (dotKernelComponent D Sc cutoff i v t)
    (dotKernelComponent_precompose D Sc cutoff i a t) n
  rw [capKernelComponent, capKernelComponent, LinearMap.comp_assoc,
    hd, ← LinearMap.comp_assoc, counitKernelComponent_precompose, LinearMap.comp_assoc]

private theorem moduleCapRow_total_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    (moduleCapRow D Sc cutoff i M n).total t z =
      ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n) z) := by
  have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i M t n) z
  change (moduleCapRow D Sc cutoff i M n).total t z =
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t
      ((inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n) z) at h
  exact h

/-- The kernel row is the fixed actual moduleCapRow, not an assumed substitute. -/
theorem capKernelComponent_moduleCapRow (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    capKernelComponent D Sc cutoff i n v t z =
      (moduleCapRow D Sc cutoff i (oldRepresentable D Sc cutoff v) n).total t
        (oldSourceKernelEquiv D Sc cutoff i v t z) := by
  rw [capKernelComponent, LinearMap.comp_apply, counitKernelComponent_apply]
  have he := transportEnd_pow_apply (oldSourceKernelEquiv D Sc cutoff i v t)
    (inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff v)) t) n z
  have hc := congrArg (unshiftedCounitComponent D Sc cutoff i v.word t.word) he
  exact hc.trans (moduleCapRow_total_apply D Sc cutoff i
    (oldRepresentable D Sc cutoff v) t n (oldSourceKernelEquiv D Sc cutoff i v t z)).symm

/-- Every fixed ordinary counit/dot-power row is an ordinary-right kernel map. -/
def capKernel (i : I) (n : ℕ) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (𝟭 (OldCategory D Sc cutoff)) t where
  app v := ModuleCat.ofHom (capKernelComponent D Sc cutoff i n v.unop t)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact capKernelComponent_precompose D Sc cutoff i n a.unop t

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-right covariance of the actual unscaled unit/dot columns

The column is exactly the chosen ordinary unit followed by an actual
induction-dot power, in canonical co-Yoneda coordinates. Its source
coefficient is composed without a parity twist.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem inductionUnitDotColumn_comp (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    inductionUnitDotColumn D Sc cutoff i v t n b =
      inductionUnitDotSign (k := k) (D.parity i) n •
        ((append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
          (Y := (⟨t⟩ : OldCategory D Sc cutoff)) b ≫
        ((ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ
          (appendMovingPower D Sc cutoff i t n) :
            (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff) ⟶
              (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) := by
  rw [inductionUnitDotColumn_apply]
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [appendOutputEmbedding_single, canonicalAppendTarget_projection]
  rfl

/-- The exact ordinary categorical unit/dot column, with no column rescaling. -/
def unitKernelComponent (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff) :
    (v ⟶ t) →ₗ[k] ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :=
  inductionUnitDotColumn D Sc cutoff i v.word t.word n

theorem unitKernelComponent_precompose (i : I) (n : ℕ)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (unitKernelComponent D Sc cutoff i n v t).comp (Linear.leftComp k t a) =
    (Linear.leftComp k ((append D Sc cutoff i).obj t) ((append D Sc cutoff i).map a)).comp
      (unitKernelComponent D Sc cutoff i n w t) := by
  apply LinearMap.ext
  intro b
  cases v with
  | mk v =>
    cases w with
    | mk w =>
      cases t with
      | mk t =>
        change inductionUnitDotColumn D Sc cutoff i v t n (a ≫ b) =
          (append D Sc cutoff i).map a ≫ inductionUnitDotColumn D Sc cutoff i w t n b
        rw [inductionUnitDotColumn_comp, inductionUnitDotColumn_comp,
          Functor.map_comp, Linear.comp_smul, Category.assoc]

/-- The actual unscaled unit/dot-power column is an ordinary-right kernel map. -/
def unitKernel (i : I) (n : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.inductionKernel (k := k) (𝟭 (OldCategory D Sc cutoff)) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) where
  app v := ModuleCat.ofHom (unitKernelComponent D Sc cutoff i n v.unop t)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact unitKernelComponent_precompose D Sc cutoff i n a.unop t

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Finite coefficient families commute with the literal kernel tensor

The finite Option(Fin m) families of DeformedMatrixComparison may be split
before or after tensoring their coefficient kernels with an arbitrary module.
The maps use explicit coordinate inclusions/projections, and both inverse
identities hold in the balanced quotient. No flatness premise occurs.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams TensorProduct
namespace OddMath.QuiverHecke.ELV.BalancedKernelTensor
universe u
variable {k C : Type u} {ι : Type} [CommRing k] [Category.{u} C]
variable (K : ι → Cᵒᵖ ⥤ ModuleCat k)

/-- Pointwise finite product of ordinary-right coefficient kernels. -/
def piKernel : Cᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (∀ a, (K a).obj v)
  map f := ModuleCat.ofHom (LinearMap.piMap (fun a => ((K a).map f).hom))
  map_id v := by
    ext x a
    change ((K a).map (𝟙 v)) (x a) = x a
    rw [(K a).map_id]
    rfl
  map_comp f g := by
    ext x a
    change ((K a).map (f ≫ g)) (x a) = ((K a).map g) (((K a).map f) (x a))
    rw [(K a).map_comp]
    rfl

def piProjection (a : ι) : piKernel K ⟶ K a where
  app _ := ModuleCat.ofHom (LinearMap.proj a)
  naturality _ _ _ := rfl

variable [DecidableEq ι]

def piInjection (a : ι) : K a ⟶ piKernel K where
  app v := ModuleCat.ofHom (LinearMap.single k (fun a => (K a).obj v) a)
  naturality {v w} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext b
    change (Pi.single a ((K a).map f x) : ∀ c, (K c).obj w) b =
      (K b).map f ((Pi.single a x : ∀ c, (K c).obj v) b)
    by_cases h : b = a
    · subst b
      simp
    · simp [h]

theorem piInjection_projection (a : ι) : piInjection K a ≫ piProjection K a = 𝟙 (K a) := by
  ext v x
  change (Pi.single a x : ∀ b, (K b).obj v) a = x
  simp

theorem piInjection_projection_ne (a b : ι) (h : b ≠ a) :
    piInjection K a ≫ piProjection K b = 0 := by
  ext v x
  change (Pi.single a x : ∀ c, (K c).obj v) b = 0
  simp [h]

variable (M : C ⥤ SVec k)

private theorem tensor_zero_left (L : Cᵒᵖ ⥤ ModuleCat k) (v : C) (m : M.obj v) :
    tensor L M v 0 m = 0 := by
  simp only [tensor, zero_tmul, map_zero]

private theorem map_zero (L P : Cᵒᵖ ⥤ ModuleCat k) :
    map M (0 : L ⟶ P) = 0 := by
  apply hom_ext
  intro v x m
  rw [map_tensor]
  exact tensor_zero_left M P v m

private theorem projection_injection (a : ι) :
    map M (piProjection K a) ∘ₗ map M (piInjection K a) = LinearMap.id := by
  rw [← map_comp, piInjection_projection, map_id]

private theorem projection_injection_ne (a b : ι) (h : b ≠ a) :
    map M (piProjection K b) ∘ₗ map M (piInjection K a) = 0 := by
  rw [← map_comp, piInjection_projection_ne K a b h, map_zero]

/-- Coordinate projections on the actual balanced quotients. -/
def toPi : Obj (piKernel K) M →ₗ[k] (∀ a, Obj (K a) M) :=
  LinearMap.pi (fun a => map M (piProjection K a))

omit [DecidableEq ι] in
@[simp] theorem toPi_tensor (v : C) (x : (piKernel K).obj (op v))
    (m : M.obj v) (a : ι) :
    toPi K M (tensor (piKernel K) M v x m) a = tensor (K a) M v (x a) m := by
  exact map_tensor M (piProjection K a) v x m

variable [Fintype ι]

/-- Coordinate inclusions summed in the actual balanced quotient. -/
def fromPi : (∀ a, Obj (K a) M) →ₗ[k] Obj (piKernel K) M :=
  ∑ a, map M (piInjection K a) ∘ₗ LinearMap.proj a

theorem fromPi_single (a : ι) (z : Obj (K a) M) :
    fromPi K M (Pi.single a z) = map M (piInjection K a) z := by
  simp only [fromPi, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  calc
    _ = map M (piInjection K a) ((Pi.single a z : ∀ b, Obj (K b) M) a) := by
      apply Finset.sum_eq_single a
      · intro b _ hb
        simp [hb]
      · simp
    _ = _ := by simp

theorem fromPi_toPi : fromPi K M ∘ₗ toPi K M = LinearMap.id := by
  apply hom_ext
  intro v x m
  change (∑ a, map M (piInjection K a) ∘ₗ LinearMap.proj a)
    (toPi K M (tensor (piKernel K) M v x m)) = tensor (piKernel K) M v x m
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    toPi_tensor, map_tensor]
  change (∑ a, inclusion (piKernel K) M v (Pi.single a (x a) ⊗ₜ[k] m)) =
    inclusion (piKernel K) M v (x ⊗ₜ[k] m)
  rw [← map_sum, ← sum_tmul, LinearMap.sum_single_apply]

theorem toPi_fromPi : toPi K M ∘ₗ fromPi K M = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext b
  change toPi K M ((∑ a, map M (piInjection K a) ∘ₗ LinearMap.proj a) x) b = x b
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
    toPi, LinearMap.pi_apply]
  calc
    _ = map M (piProjection K b) (map M (piInjection K b) (x b)) := by
      apply Finset.sum_eq_single b
      · intro a _ hab
        exact LinearMap.congr_fun (projection_injection_ne K M a b (Ne.symm hab)) (x a)
      · simp
    _ = x b := LinearMap.congr_fun (projection_injection K M b) (x b)

/-- Finite coefficient products commute with kernel tensor, without flatness. -/
def piEquiv : Obj (piKernel K) M ≃ₗ[k] (∀ a, Obj (K a) M) :=
  LinearEquiv.ofLinearMap (toPi K M) (fromPi K M) (toPi_fromPi K M) (fromPi_toPi K M)

@[simp] theorem piEquiv_tensor (v : C) (x : (piKernel K).obj (op v))
    (m : M.obj v) (a : ι) :
    piEquiv K M (tensor (piKernel K) M v x m) a = tensor (K a) M v (x a) m :=
  toPi_tensor K M v x m a

@[simp] theorem piEquiv_symm_single (a : ι) (z : Obj (K a) M) :
    (piEquiv K M).symm (Pi.single a z) = map M (piInjection K a) z :=
  fromPi_single K M a z

end OddMath.QuiverHecke.ELV.BalancedKernelTensor
end

end

section

/-! # Actual finite matrix component maps and their parity
Brundan--Ellis (1.13)--(1.14) assemble the prescribed even module
entries on the actual finite parity-shifted superspace families.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.MatrixComponentParity
universe u
variable {k : Type u} [CommRing k]
variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem total_even {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (hf : f ∈ parity (R := k) F G 0) (t : C) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t
  have ht : f.total t = f.app 0 t := by
    rw [SuperNatTrans.total, hz, add_zero]
  rw [ht]
  exact f.app_mem 0 t

private theorem inverse_precompose_total {F G H : Superfunctor k C (SVec k)}
    (e : F ≅ G) (f : F ⟶ H) (t : C) (z : G.obj t) :
    f.total t ((moduleIsoLinearEquiv e t).symm z) = (e.inv ≫ f).total t z := by
  rw [Superfunctor.comp_total]
  rfl

private theorem postcompose_total {F G H : Superfunctor k C (SVec k)}
    (e : G ≅ H) (f : F ⟶ G) (t : C) (z : F.obj t) :
    moduleIsoLinearEquiv e t (f.total t z) = (f ≫ e.hom).total t z := by
  rw [Superfunctor.comp_total]
  rfl

end OddMath.QuiverHecke.ELV.MatrixComponentParity

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual finite source superspace with its pointwise shifted grading. -/
def unitMatrixSourceSpace (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t

/-- The actual finite target superspace with its pointwise shifted grading. -/
def capMatrixTargetSpace (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (capMatrixFamily D Sc cutoff i M m a).obj t

/-- Finite assembly of the actual unit-family entries. -/
def unitMatrixComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    unitMatrixSourceSpace D Sc cutoff i M m t ⟶
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t :=
  OddMath.FiniteSuperspace.assembleColumns _ _
    fun a => (unitMatrixEntry D Sc cutoff i M m a).total t

/-- Finite assembly of the actual cap-family entries. -/
def capMatrixComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t ⟶
        capMatrixTargetSpace D Sc cutoff i M m t :=
  OddMath.FiniteSuperspace.assembleRows _ _
    fun a => (capMatrixEntry D Sc cutoff i M m a).total t

/-- The actual finite unit matrix is even, for every old module. -/
theorem unitMatrixComponent_even (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    unitMatrixComponent D Sc cutoff i M m t ∈ parity (R := k) _ _ 0 := by
  apply OddMath.FiniteSuperspace.assembleColumns_even
  intro a
  exact MatrixComponentParity.total_even _ (unitMatrixEntry_mem D Sc cutoff i M m a) t

local instance finiteMatrixComponentsPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The canonical first source parity isomorphism with fixed literal module endpoints. -/
def unitMatrixFirstSourceIso (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    unitMatrixFamily D Sc cutoff i M m none ≅
      (BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) :=
  (SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M))

/-- Removing the canonical first source shift gives the actual mate as a module map. -/
theorem unitMatrixEntry_none_unshifted (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    (unitMatrixFirstSourceIso D Sc cutoff i M m).inv ≫
      unitMatrixEntry D Sc cutoff i M m none = matrixMateComponent D Sc cutoff i M := by
  rw [unitMatrixFirstSourceIso, unitMatrixEntry_none, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The literal first unit entry agrees with the mate after the canonical source coordinate. -/
theorem unitMatrixEntry_none_inverse_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      ((moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t).symm z) =
      (matrixMateComponent D Sc cutoff i M).total t z := by
  have h := MatrixComponentParity.inverse_precompose_total
    (unitMatrixFirstSourceIso D Sc cutoff i M m)
    (unitMatrixEntry D Sc cutoff i M m none) t z
  rw [unitMatrixEntry_none_unshifted] at h
  exact h

/-- The first literal unit entry uses the canonical source parity coordinate. -/
theorem unitMatrixEntry_none_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (b : (unitMatrixFamily D Sc cutoff i M m none).obj t) :
    (unitMatrixEntry D Sc cutoff i M m none).total t b =
      (matrixMateComponent D Sc cutoff i M).total t
        (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t b) := by
  have h := unitMatrixEntry_none_inverse_apply D Sc cutoff i M m t
    (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t b)
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- The canonical first target parity isomorphism with fixed literal module endpoints. -/
def capMatrixFirstTargetIso (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixFamily D Sc cutoff i M m none ≅
      (BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  (SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj M))

/-- The literal first cap entry before evaluating components. -/
theorem capMatrixEntry_none (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixEntry D Sc cutoff i M m none =
      matrixMateComponent D Sc cutoff i M ≫ (capMatrixFirstTargetIso D Sc cutoff i M m).inv := rfl

/-- Removing the canonical first target parity gives the actual mate as a module map. -/
theorem capMatrixEntry_none_unshifted (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixEntry D Sc cutoff i M m none ≫ (capMatrixFirstTargetIso D Sc cutoff i M m).hom =
      matrixMateComponent D Sc cutoff i M := by
  rw [capMatrixEntry_none, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal first cap entry uses the canonical target parity coordinate. -/
theorem capMatrixEntry_none_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      ((capMatrixEntry D Sc cutoff i M m none).total t z) =
      (matrixMateComponent D Sc cutoff i M).total t z := by
  have h := MatrixComponentParity.postcompose_total (capMatrixFirstTargetIso D Sc cutoff i M m)
    (capMatrixEntry D Sc cutoff i M m none) t z
  rw [capMatrixEntry_none_unshifted] at h
  exact h

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

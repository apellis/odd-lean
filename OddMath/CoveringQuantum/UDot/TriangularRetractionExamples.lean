/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.GlobalTriangular
import OddMath.CoveringQuantum.UDot.TriangularRepresentationExamples

/-!
# Triangular and global recovery with infinitely many even colours

On the infinite, non-bar-consistent datum of `VermaWeightExamples`, the existing
half retractions and triangular equivalences recover generated quotient tensors.
A finite inhomogeneous family uses two distinct right weights, one negative.
These coordinates support the unrestricted form construction in [BE2, §10]; they
assert neither individual representation faithfulness nor form nondegeneracy.
The [CHW1, §2.3] motivation does not replace the BE2 quantum integers or scalar bar.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.TriangularRetractionExamples
open Coefficients TensorProduct GenericTensor VermaWeightExamples
open TriangularRepresentationExamples

local notation "H" => datum.serreF Coefficients.q pi

/-- The example is genuinely infinite and fails the former bar-consistency premise. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- The chosen right weight has negative colour-zero pairing. -/
theorem baseWeight_pairing : datum.h 0 baseWeight = -3 := by
  simp [baseWeight, datum, RootDatum.h]

/-- The two right weights in the family are distinct. -/
theorem baseWeight_ne_zero : baseWeight ≠ 0 := by
  intro h
  have h0 := congrArg (fun μ : ℕ →₀ ℤ ↦ μ 0) h
  norm_num [baseWeight] at h0

/-- A generated, inhomogeneous half input with a non-bar-fixed scalar. -/
def halfInput : H := generator 0 + (Coefficients.q : Coefficients.Ring) • (1 : H)

/-- Vacuum evaluation retracts the negative half at the negative right weight. -/
theorem negative_recovery :
    negativeRetraction datum baseWeight
      (negativeHalf datum Coefficients.q pi baseWeight halfInput) = halfInput :=
  negativeRetraction_half datum baseWeight halfInput

/-- The two BE2 scalar bars cancel in the positive linear retraction. -/
theorem positive_recovery :
    positiveRetraction datum baseWeight
      (positiveHalf datum Coefficients.q pi baseWeight halfInput) = halfInput :=
  positiveRetraction_half datum baseWeight halfInput

/-- Both existing half maps are injective at this right weight. -/
theorem half_injective :
    Function.Injective (negativeHalf datum Coefficients.q pi baseWeight) ∧
      Function.Injective (positiveHalf datum Coefficients.q pi baseWeight) :=
  ⟨negativeHalf_injective datum baseWeight, positiveHalf_injective datum baseWeight⟩

/-- The tensor has a generated term and a vacuum term; no nonzero assertion. -/
def inhomogeneous : H ⊗[Coefficients.Ring] H :=
  generated + (1 : H) ⊗ₜ[Coefficients.Ring] (1 : H)

/-- Concrete tensor evaluation retracts the existing matched multiplication. -/
theorem tensor_recovery :
    tensorEval datum baseWeight
      (triangularTensor datum Coefficients.q pi baseWeight inhomogeneous) = inhomogeneous :=
  tensorEval_triangularTensor datum baseWeight inhomogeneous

/-- The fixed-column inverse recovers a generated inhomogeneous tensor. -/
theorem column_left_roundtrip :
    (triangularColumnEquiv datum baseWeight).symm
      (triangularColumnEquiv datum baseWeight inhomogeneous) = inhomogeneous :=
  (triangularColumnEquiv datum baseWeight).symm_apply_apply inhomogeneous

/-- The reverse roundtrip recovers its actual modified-algebra column. -/
theorem column_right_roundtrip :
    triangularColumnEquiv datum baseWeight
      ((triangularColumnEquiv datum baseWeight).symm
        (triangularColumn datum Coefficients.q pi baseWeight inhomogeneous)) =
      triangularColumn datum Coefficients.q pi baseWeight inhomogeneous :=
  (triangularColumnEquiv datum baseWeight).apply_symm_apply _

/-- A finite family at two distinct right weights, with inhomogeneous tensor values. -/
def family : (ℕ →₀ ℤ) →₀ H ⊗[Coefficients.Ring] H :=
  Finsupp.single baseWeight inhomogeneous +
    Finsupp.single 0 ((Coefficients.q : Coefficients.Ring) • generated)

/-- Its negative-weight coordinate is the specified inhomogeneous tensor. -/
theorem family_negative : family baseWeight = inhomogeneous := by
  simp [family, baseWeight_ne_zero]

/-- Its zero-weight coordinate is the specified scalar multiple of a generated tensor. -/
theorem family_zero : family 0 = (Coefficients.q : Coefficients.Ring) • generated := by
  simp [family, baseWeight_ne_zero]

/-- Explicit global coordinates recover the entire finite family. -/
theorem coordinates_recovery : triangularCoordinates datum (globalTriangular datum family) =
    family :=
  triangularCoordinates_globalTriangular datum family

/-- Matched multiplication of those coordinates recovers the modified element. -/
theorem modified_recovery :
    globalTriangular datum (triangularCoordinates datum (globalTriangular datum family)) =
      globalTriangular datum family :=
  globalTriangular_triangularCoordinates datum _

/-- The global equivalence's source roundtrip on this finite inhomogeneous family. -/
theorem global_left_roundtrip :
    (globalTriangularEquiv datum).symm (globalTriangularEquiv datum family) = family :=
  (globalTriangularEquiv datum).symm_apply_apply family

/-- The global equivalence's target roundtrip on the actual sum of matched products. -/
theorem global_right_roundtrip :
    globalTriangularEquiv datum
      ((globalTriangularEquiv datum).symm (globalTriangular datum family)) =
      globalTriangular datum family :=
  (globalTriangularEquiv datum).apply_symm_apply _

/-- Joint separation is proved for the representation family, not assumed for one member. -/
theorem representation_criterion (x y : modified datum Coefficients.q pi) :
    x = y ↔ ∀ μ, modifiedRepresentation datum μ x = modifiedRepresentation datum μ y :=
  eq_iff_modifiedRepresentation datum x y

/-- The criterion applies in particular to the constructed finite sum of matched products. -/
theorem family_criterion (x : modified datum Coefficients.q pi) :
    x = globalTriangular datum family ↔
      ∀ μ, modifiedRepresentation datum μ x =
        modifiedRepresentation datum μ (globalTriangular datum family) :=
  representation_criterion x _

end OddMath.CoveringQuantum.UDot.TriangularRetractionExamples

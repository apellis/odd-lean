/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ModifiedForm
import OddMath.CoveringQuantum.UDot.TriangularRetractionExamples

/-!
# Constructed bilinear form on an infinite non-bar-consistent datum

The existing modified form evaluates on quotient inputs at a negative right weight.
This tests an intermediate construction for the form in BE2, arXiv:1701.04133v2,
Theorem 10.1, used by the graphical Theorem 10.3; sesquilinear transport remains
separate. Clark, arXiv:1312.4855v2, Theorem 5.2 supplies the construction pattern
under narrower ambient hypotheses.
No nondegeneracy or nonvanishing of the generated quotient inputs is asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.ModifiedFormExamples
open Coefficients GenericTensor VermaWeightExamples TriangularRepresentationExamples

local notation "H" => datum.serreF Coefficients.q pi
local notation "M" => modified datum Coefficients.q pi

/-- Applicability is on the infinite datum, not a finite-colour restriction. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- The right weight has negative colour-zero pairing. -/
theorem negative_weight : datum.h 0 baseWeight = -3 :=
  TriangularRetractionExamples.baseWeight_pairing

/-- Two generated quotient inputs with terms of distinct degrees. -/
def firstHalf : H := generator 0 + (Coefficients.q : Coefficients.Ring) • (1 : H)

/-- The second input uses a distinct colour and a nonconstant coefficient. -/
def secondHalf : H := generator 1 + (Coefficients.q : Coefficients.Ring) • generator 0

/-- The positive-column normalization applies to the two inhomogeneous inputs. -/
theorem positive_normalization :
    columnFunctional datum baseWeight
      ((rho datum Coefficients.q pi pi_sq
        (halfMap datum Coefficients.q pi true baseWeight firstHalf)).unop *
          halfMap datum Coefficients.q pi true baseWeight secondHalf) =
      datum.serreForm Coefficients.q pi pi_sq firstHalf secondHalf :=
  columnFunctional_rho_halfMap datum baseWeight firstHalf secondHalf

/-- Evaluation of the constructed form, with its original half-form normalization. -/
theorem negative_normalization :
    modifiedForm datum
      (negativeHalf datum Coefficients.q pi baseWeight firstHalf)
      (negativeHalf datum Coefficients.q pi baseWeight secondHalf) =
      datum.serreForm Coefficients.q pi pi_sq firstHalf secondHalf :=
  modifiedForm_negativeHalf datum baseWeight firstHalf secondHalf

/-- The half-unit at a right weight is the actual local idempotent. -/
def localUnit (μ : ℕ →₀ ℤ) : M := negativeHalf datum Coefficients.q pi μ 1

/-- The local unit has scalar norm one. -/
theorem unit_normalization :
    modifiedForm datum (localUnit baseWeight) (localUnit baseWeight) = 1 := by
  rw [localUnit, modifiedForm_negativeHalf, SuperCartanDatum.serreForm_one_one]

/-- An adjoint equation on generated inhomogeneous modified-algebra inputs. -/
theorem adjoint_evaluation :
    modifiedForm datum
      (negativeHalf datum Coefficients.q pi baseWeight firstHalf * localUnit baseWeight)
      (negativeHalf datum Coefficients.q pi baseWeight secondHalf) =
    modifiedForm datum (localUnit baseWeight)
      (rhoModified datum Coefficients.q pi pi_sq
        (negativeHalf datum Coefficients.q pi baseWeight firstHalf) *
          negativeHalf datum Coefficients.q pi baseWeight secondHalf) :=
  modifiedForm_adjoint datum _ _ _

private theorem localUnit_mem_block (μ : ℕ →₀ ℤ) :
    (localUnit μ : CoveringUDot Coefficients.Ring datum Coefficients.q pi) ∈
      block datum Coefficients.q pi μ μ := by
  change halfMap datum Coefficients.q pi false μ 1 ∈ _
  rw [halfMap_one]
  exact ⟨one_mul_one_self datum Coefficients.q pi μ, one_mul_one_self datum Coefficients.q pi μ⟩

/-- Distinct negative and zero weights are orthogonal by the left endpoints. -/
theorem left_orthogonality :
    modifiedForm datum (localUnit baseWeight) (localUnit 0) = 0 :=
  modifiedForm_orthogonal datum baseWeight baseWeight 0 0 _ _
    (localUnit_mem_block _) (localUnit_mem_block _)
    (Or.inl TriangularRetractionExamples.baseWeight_ne_zero)

/-- The right-endpoint branch also applies to these two actual diagonal blocks. -/
theorem right_orthogonality :
    modifiedForm datum (localUnit baseWeight) (localUnit 0) = 0 :=
  modifiedForm_orthogonal datum baseWeight baseWeight 0 0 _ _
    (localUnit_mem_block _) (localUnit_mem_block _)
    (Or.inr TriangularRetractionExamples.baseWeight_ne_zero)

end OddMath.CoveringQuantum.UDot.ModifiedFormExamples

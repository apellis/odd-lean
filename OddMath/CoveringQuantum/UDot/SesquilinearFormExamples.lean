/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.SesquilinearForm
import OddMath.CoveringQuantum.UDot.ModifiedFormExamples

/-!
# Sesquilinear evaluation on infinite non-bar-consistent data

The form of BE2, arXiv:1701.04133v2, Theorem 10.1 evaluates on the existing
infinite datum at a negative weight, with inhomogeneous generated inputs and a
non-bar-fixed scalar. This supplies concrete form evaluations for consumers of
Theorem 10.3; the graphical identity is not proved in this module.

The coefficient ring is the generic covering ring. The datum has Nat colours,
finitely supported integral weights, even parity and symmetrizer one. There is
no form-existence, compatibility, root-separation or nondegeneracy premise.
No nonzero claim about the generated inputs is made. Clark, arXiv:1312.4855v2,
Theorem 5.2 and Proposition 5.8 use narrower finite, bar-consistent ambient data
and different normalization conventions; they are not identified with this form.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.SesquilinearFormExamples
open Coefficients GenericTensor VermaWeightExamples TriangularRepresentationExamples
open ModifiedFormExamples

local notation "M" => modified datum Coefficients.q pi

/-- Infinite colours and failure of bar consistency are both proved for this datum. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ModifiedFormExamples.infinite_nonbar

/-- The chosen right weight has negative colour-zero pairing. -/
theorem negative_weight : datum.h 0 baseWeight = -3 :=
  ModifiedFormExamples.negative_weight

/-- A positive-half input with a generator and a scalar multiple of the half-unit. -/
def firstInput : M := positiveHalf datum Coefficients.q pi baseWeight firstHalf

/-- A second generated positive-half input, with a distinct colour. -/
def secondInput : M := positiveHalf datum Coefficients.q pi baseWeight secondHalf

/-- Positive normalization for the bilinear precursor uses no bar on either input. -/
theorem positive_normalization :
    positiveModifiedForm datum firstInput secondInput =
      datum.serreForm Coefficients.q pi pi_sq firstHalf secondHalf :=
  positiveModifiedForm_positiveHalf datum baseWeight firstHalf secondHalf

/-- The sesquilinear evaluation conjugates the entire first half-algebra input. -/
theorem evaluation :
    sesquilinearForm datum firstInput secondInput =
      datum.serreForm Coefficients.q pi pi_sq (GenericVerma.halfBar datum firstHalf)
        secondHalf :=
  sesquilinearForm_positiveHalf datum baseWeight firstHalf secondHalf

/-- The first slot conjugates the nonconstant scalar q. -/
theorem first_slot_scaling :
    sesquilinearForm datum ((Coefficients.q : Coefficients.Ring) • firstInput) secondInput =
      bar (Coefficients.q : Coefficients.Ring) *
        sesquilinearForm datum firstInput secondInput := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

/-- The second slot is linear, not conjugate-linear. -/
theorem second_slot_scaling :
    sesquilinearForm datum firstInput ((Coefficients.q : Coefficients.Ring) • secondInput) =
      (Coefficients.q : Coefficients.Ring) *
        sesquilinearForm datum firstInput secondInput := by
  simp only [map_smul, smul_eq_mul]

/-- The generic coefficient q is not fixed by the specified bar involution. -/
theorem q_not_bar_fixed : bar (Coefficients.q : Coefficients.Ring) ≠
    (Coefficients.q : Coefficients.Ring) := by
  intro h
  have hs : (Coefficients.q : Coefficients.Ring) ^ 2 = 1 := by
    calc
      _ = (Coefficients.q : Coefficients.Ring) *
          bar (Coefficients.q : Coefficients.Ring) := by rw [h, pow_two]
      _ = 1 := by rw [bar_q]; exact Units.mul_inv Coefficients.q
  have hz : IsUnit (0 : Coefficients.Ring) := by
    simpa only [one_mul, hs, sub_self] using
      (one_sub_isUnit 1 (by simp) (n := 2) (by decide))
  exact not_isUnit_zero hz

/-- The positive half-unit is the local idempotent at the selected weight. -/
def unitInput (μ : ℕ →₀ ℤ) : M := positiveHalf datum Coefficients.q pi μ 1

/-- Its sesquilinear value is one, including at the negative weight. -/
theorem unit_value :
    sesquilinearForm datum (unitInput baseWeight) (unitInput baseWeight) = 1 := by
  have h : GenericVerma.halfBar datum 1 = 1 := by
    simpa using GenericVerma.halfBar_monomial datum []
  rw [unitInput, sesquilinearForm_positiveHalf, h, SuperCartanDatum.serreForm_one_one]

/-- Scalar-slot evaluations are genuinely distinct on the local unit. -/
theorem scalar_slots_distinct :
    sesquilinearForm datum ((Coefficients.q : Coefficients.Ring) • unitInput baseWeight)
      (unitInput baseWeight) ≠
    sesquilinearForm datum (unitInput baseWeight)
      ((Coefficients.q : Coefficients.Ring) • unitInput baseWeight) := by
  simpa only [map_smulₛₗ, LinearMap.smul_apply, map_smul, unit_value, smul_eq_mul,
    mul_one, RingHom.id_apply] using q_not_bar_fixed

/-- Original-star adjointness on the inhomogeneous generated inputs. -/
theorem star_adjoint_evaluation :
    sesquilinearForm datum (firstInput * unitInput baseWeight) secondInput =
      sesquilinearForm datum (unitInput baseWeight)
        (starModified datum firstInput * secondInput) :=
  sesquilinearForm_adjoint datum _ _ _

/-- Original-shriek adjointness is also available without a compatibility premise. -/
theorem shriek_adjoint_evaluation :
    sesquilinearForm datum firstInput (secondInput * unitInput baseWeight) =
      sesquilinearForm datum (shriekModified datum secondInput * firstInput)
        (unitInput baseWeight) :=
  sesquilinearForm_shriek_adjoint datum _ _ _

/-- The psi-reversal symmetry applies to these nonhomogeneous inputs. -/
theorem reversal_evaluation :
    sesquilinearForm datum firstInput secondInput =
      sesquilinearForm datum (psiModified datum secondInput) (psiModified datum firstInput) :=
  sesquilinearForm_psi_comm datum _ _

private theorem unitInput_mem_block (μ : ℕ →₀ ℤ) :
    (unitInput μ : CoveringUDot Coefficients.Ring datum Coefficients.q pi) ∈
      block datum Coefficients.q pi μ μ := by
  change halfMap datum Coefficients.q pi true μ 1 ∈ _
  rw [halfMap_one]
  exact ⟨one_mul_one_self datum Coefficients.q pi μ,
    one_mul_one_self datum Coefficients.q pi μ⟩

/-- Distinct left endpoints give zero for the negative and zero local weights. -/
theorem left_orthogonality :
    sesquilinearForm datum (unitInput baseWeight) (unitInput 0) = 0 :=
  sesquilinearForm_orthogonal datum baseWeight baseWeight 0 0 _ _
    (unitInput_mem_block _) (unitInput_mem_block _)
    (Or.inl TriangularRetractionExamples.baseWeight_ne_zero)

/-- The right-endpoint orthogonality branch evaluates the same two diagonal blocks. -/
theorem right_orthogonality :
    sesquilinearForm datum (unitInput baseWeight) (unitInput 0) = 0 :=
  sesquilinearForm_orthogonal datum baseWeight baseWeight 0 0 _ _
    (unitInput_mem_block _) (unitInput_mem_block _)
    (Or.inr TriangularRetractionExamples.baseWeight_ne_zero)

end OddMath.CoveringQuantum.UDot.SesquilinearFormExamples

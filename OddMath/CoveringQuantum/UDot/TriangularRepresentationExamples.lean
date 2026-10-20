/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TriangularRepresentation
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Regular modified actions with infinitely many even colours

The datum of `VermaWeightExamples` has infinitely many colours and fails bar
consistency. The actual modified idempotent and both Chevalley generators are
computed on a tensor generated in both factors, with negative colour-zero weight.
The construction retains the [BE2, §10] conventions; [CHW1, §2.3] motivates the
regular tensor construction but uses different quantum-integer and bar conventions.
No nonvanishing, faithfulness, form compatibility or nondegeneracy is asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.TriangularRepresentationExamples
open PreF Coefficients TensorProduct GenericTensor VermaWeightExamples

local notation "H" => datum.serreF Coefficients.q pi

/-- The class of a generator in the source Serre quotient. -/
def generator (i : ℕ) : H := datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i)

/-- A negative parameter weight. -/
def baseWeight : ℕ →₀ ℤ := Finsupp.single 0 (-3)

/-- A tensor generated in both quotient factors; no nonzero assertion. -/
def generated : H ⊗[Coefficients.Ring] H :=
  generator 0 ⊗ₜ[Coefficients.Ring] generator 1

/-- The actual weight of the generated tensor. -/
def inputWeight : ℕ →₀ ℤ := baseWeight - datum.α 0 + datum.α 1

/-- The colour set is infinite and the root datum is not bar consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- The generated input has strictly negative colour-zero pairing. -/
theorem inputWeight_pairing : datum.h 0 inputWeight = -5 := by
  simp [inputWeight, baseWeight, datum, RootDatum.h, RootDatum.α]

/-- Tensor projection uses the actual total weight of arbitrary monomial images. -/
theorem project_monomial (Λ μ : ℕ →₀ ℤ) (a b : List ℕ) :
    weightProject datum Λ μ
      (datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) =
      if Λ - halfWeight datum true (wordWeight a) + halfWeight datum true (wordWeight b) = μ
      then datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring b) else 0 :=
  weightProject_monomial datum Λ μ a b

/-- The projector fixes the generated tensor at its actual weight. -/
theorem project_generated : weightProject datum baseWeight inputWeight generated = generated := by
  simpa [generated, generator, inputWeight, monomial_cons, halfRoot] using
    project_monomial baseWeight inputWeight [0] [1]

private theorem project_right :
    weightProject datum baseWeight (baseWeight + datum.α 1)
      ((1 : H) ⊗ₜ[Coefficients.Ring] generator 1) =
      (1 : H) ⊗ₜ[Coefficients.Ring] generator 1 := by
  simpa [generator, monomial_cons, halfRoot] using
    project_monomial baseWeight (baseWeight + datum.α 1) [] [1]

/-- The regular positive operator includes creation and the exact `[-3]` correction. -/
theorem positive_generated :
    positive datum.toSuperCartanDatum (fun i ↦ datum.h i baseWeight) 0 generated =
      generator 0 ⊗ₜ[Coefficients.Ring] (generator 0 * generator 1) +
        qpInt (datum.qi Coefficients.q 0) (datum.pii pi 0) (-3) •
          ((1 : H) ⊗ₜ[Coefficients.Ring] generator 1) := by
  have h := positive_negative_project datum baseWeight (baseWeight + datum.α 1) 0 0
    ((1 : H) ⊗ₜ[Coefficients.Ring] generator 1)
  rw [project_right] at h
  simpa [negative_tmul, positive_one_tmul, generated, generator, datum,
    RootDatum.h, RootDatum.α, baseWeight] using h

/-- The nonunital modified idempotent fixes the generated tensor. -/
theorem modified_idempotent_generated :
    modifiedRepresentation datum baseWeight
      ⟨one datum Coefficients.q pi inputWeight,
        one_mem_modified datum Coefficients.q pi inputWeight⟩ generated = generated := by
  change representation datum baseWeight (one datum Coefficients.q pi inputWeight) _ = _
  rw [representation_one, project_generated]

/-- The nonunital negative generator multiplies the first generated factor. -/
theorem modified_negative_generated :
    modifiedRepresentation datum baseWeight
      ⟨F datum Coefficients.q pi 0 inputWeight,
        F_mem_modified datum Coefficients.q pi 0 inputWeight⟩ generated =
      (generator 0 * generator 0) ⊗ₜ[Coefficients.Ring] generator 1 := by
  change representation datum baseWeight (F datum Coefficients.q pi 0 inputWeight) _ = _
  rw [representation_F, Module.End.mul_apply, project_generated]
  rfl

/-- The nonunital positive action has both the creation and lowering terms. -/
theorem modified_positive_generated :
    modifiedRepresentation datum baseWeight
      ⟨E datum Coefficients.q pi 0 inputWeight,
        E_mem_modified datum Coefficients.q pi 0 inputWeight⟩ generated =
      generator 0 ⊗ₜ[Coefficients.Ring] (generator 0 * generator 1) +
        qpInt (datum.qi Coefficients.q 0) (datum.pii pi 0) (-3) •
          ((1 : H) ⊗ₜ[Coefficients.Ring] generator 1) := by
  change representation datum baseWeight (E datum Coefficients.q pi 0 inputWeight) _ = _
  rw [representation_E, Module.End.mul_apply, project_generated, positive_generated]

end OddMath.CoveringQuantum.UDot.TriangularRepresentationExamples

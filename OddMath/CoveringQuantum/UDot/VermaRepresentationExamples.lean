/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaRepresentation
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Highest-weight actions with infinitely many even colours

The generator and weight equations of [BE2, §10] are exercised on the Serre
quotient for `VermaWeightExamples.datum`, with highest weight supported at colour
zero and pairing `-3`. The nonunital modified-algebra action is evaluated on its
idempotent and both Chevalley generators. No faithfulness or nondegeneracy is
asserted. The highest-weight construction follows [CHW1, §2.3], in the existing
[BE2] normalization rather than the different quantum-integer convention of [CHW1].
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.VermaRepresentationExamples
open PreF Coefficients GenericVerma VermaWeightExamples

/-- A negative highest weight in the finitely supported weight group. -/
def highestWeight : ℕ →₀ ℤ := Finsupp.single 0 (-3)

/-- This consumer has infinitely many colours and fails bar consistency. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- Its colour-zero pairing is negative. -/
theorem highestWeight_pairing : datum.h 0 highestWeight = -3 := by
  simp [highestWeight, datum, RootDatum.h]

/-- The highest-weight projection fixes the quotient vacuum. -/
theorem project_vacuum (Λ : ℕ →₀ ℤ) :
    weightProject datum Λ Λ (1 : datum.serreF Coefficients.q pi) = 1 := by
  rw [← map_one (datum.toSerreF Coefficients.q pi), weightProject_mk]
  change datum.toSerreF Coefficients.q pi
    (weightProjectFree datum Λ Λ (monomial Coefficients.Ring [])) = _
  rw [weightProjectFree_monomial]
  simp

/-- Multiplication by a negative generator lowers its quotient weight. -/
theorem project_generator (Λ : ℕ →₀ ℤ) (i : ℕ) :
    weightProject datum Λ (Λ - datum.α i)
      (datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
        datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i) := by
  calc
    _ = weightProject datum Λ (Λ - datum.α i)
        (datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * 1) := by rw [mul_one]
    _ = datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i) *
        weightProject datum Λ Λ 1 := by rw [weightProject_θ_mul, sub_add_cancel]
    _ = _ := by rw [project_vacuum, mul_one]

/-- The descended idempotents remain orthogonal at arbitrary weights. -/
theorem project_orthogonal (Λ μ ν : ℕ →₀ ℤ) :
    weightProject datum Λ μ * weightProject datum Λ ν =
      if μ = ν then weightProject datum Λ μ else 0 :=
  weightProject_mul datum Λ μ ν

/-- The envelope's negative generator acts on the vacuum by its quotient class. -/
theorem negative_vacuum (i : ℕ) :
    representation datum highestWeight (F datum Coefficients.q pi i highestWeight) 1 =
      datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i) := by
  rw [representation_F, project_vacuum, mul_one]

/-- The positive generator annihilates the quotient vacuum. -/
theorem positive_vacuum (i : ℕ) :
    representation datum highestWeight (E datum Coefficients.q pi i highestWeight) 1 = 0 := by
  rw [representation_E, Module.End.mul_apply, project_vacuum, lower_one]

/-- The positive generator on the colour-zero vector has quantum integer `[-3]`. -/
theorem positive_generator :
    representation datum highestWeight
      (E datum Coefficients.q pi 0 (highestWeight - datum.α 0))
      (datum.toSerreF Coefficients.q pi (θ Coefficients.Ring 0)) =
        qpInt (datum.qi Coefficients.q 0) (datum.pii pi 0) (-3) •
          (1 : datum.serreF Coefficients.q pi) := by
  rw [representation_E, Module.End.mul_apply, project_generator, lower_θ_self,
    highestWeight_pairing]

/-- The weight idempotent in the nonunital modified algebra fixes the vacuum. -/
theorem modified_idempotent_vacuum :
    modifiedRepresentation datum highestWeight
      ⟨one datum Coefficients.q pi highestWeight,
        one_mem_modified datum Coefficients.q pi highestWeight⟩ 1 = 1 := by
  change representation datum highestWeight
    (one datum Coefficients.q pi highestWeight) 1 = 1
  rw [representation_one, project_vacuum]

/-- The nonunital modified algebra has the same negative-generator action. -/
theorem modified_negative_vacuum (i : ℕ) :
    modifiedRepresentation datum highestWeight
      ⟨F datum Coefficients.q pi i highestWeight,
        F_mem_modified datum Coefficients.q pi i highestWeight⟩ 1 =
      datum.toSerreF Coefficients.q pi (θ Coefficients.Ring i) := by
  change representation datum highestWeight
    (F datum Coefficients.q pi i highestWeight) 1 = _
  exact negative_vacuum i

/-- The nonunital positive action uses the shifted, negative input weight. -/
theorem modified_positive_generator :
    modifiedRepresentation datum highestWeight
      ⟨E datum Coefficients.q pi 0 (highestWeight - datum.α 0),
        E_mem_modified datum Coefficients.q pi 0 (highestWeight - datum.α 0)⟩
      (datum.toSerreF Coefficients.q pi (θ Coefficients.Ring 0)) =
        qpInt (datum.qi Coefficients.q 0) (datum.pii pi 0) (-3) •
          (1 : datum.serreF Coefficients.q pi) := by
  change representation datum highestWeight
    (E datum Coefficients.q pi 0 (highestWeight - datum.α 0)) _ = _
  exact positive_generator

end OddMath.CoveringQuantum.UDot.VermaRepresentationExamples

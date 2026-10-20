/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TriangularSerre
import OddMath.CoveringQuantum.SerreDerivExamples

/-!
# Infinite-colour regular tensor operators

The orthogonal even datum on `ℕ` is not bar consistent. Its actual Serre quotient
supports the two regular half-actions, with arbitrary integer-valued weight
parameters. The positive Serre identity is tested on two generated inputs, not
only on a first-factor vacuum. No nonvanishing of these inputs is asserted.

These are direct Serre-quotient instances of the regular construction motivated
by [CHW1] v2 §2.3, in the quantum-integer convention of [BE2] §10. They assert
neither faithfulness nor a modified-form identity or nondegeneracy theorem.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot.TriangularOperatorExamples

open PreF Coefficients SerreDerivExamples TensorProduct

local notation "H" => orthogonalEven.serreF Coefficients.q pi

/-- The ambient colour set is infinite and the datum is not bar consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ orthogonalEven.BarConsistent :=
  ⟨infinite_colours, orthogonalEven_not_barConsistent⟩

/-- A two-generator input in the first actual Serre quotient; no nonvanishing claim. -/
def generatedLeft : H :=
  orthogonalEven.toSerreF Coefficients.q pi
    (θ Coefficients.Ring 0 * θ Coefficients.Ring 2)

/-- A two-generator input in the second actual Serre quotient; no nonvanishing claim. -/
def generatedRight : H :=
  orthogonalEven.toSerreF Coefficients.q pi
    (θ Coefficients.Ring 1 * θ Coefficients.Ring 3)

/-- Positive Serre is an endomorphism identity on the entire actual tensor product. -/
theorem positive_serre (n : ℕ → ℤ) :
    GenericTensor.positiveFree orthogonalEven n
      (orthogonalEven.serreElt Coefficients.q pi 0 1) = 0 :=
  GenericTensor.positive_serre orthogonalEven n 0 1 (by decide)

/-- The full positive Serre operator annihilates a tensor of two generated inputs. -/
theorem positive_serre_generated (n : ℕ → ℤ) :
    GenericTensor.positiveFree orthogonalEven n
      (orthogonalEven.serreElt Coefficients.q pi 0 1)
      (generatedLeft ⊗ₜ[Coefficients.Ring] generatedRight) = 0 := by
  rw [positive_serre, LinearMap.zero_apply]

/-- The explicit sum of regular positive operators vanishes on the generated tensor. -/
theorem positive_serre_sum_generated (n : ℕ → ℤ) :
    (∑ r ∈ Finset.range (orthogonalEven.serreDeg 0 1 + 1),
      orthogonalEven.serreCoeff Coefficients.q pi 0 1 r •
        (GenericTensor.positive orthogonalEven n 0 ^ (orthogonalEven.serreDeg 0 1 - r) *
          GenericTensor.positive orthogonalEven n 1 *
          GenericTensor.positive orthogonalEven n 0 ^ r))
      (generatedLeft ⊗ₜ[Coefficients.Ring] generatedRight) = 0 := by
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow,
    GenericTensor.positiveFree_θ] using positive_serre_generated n

/-- The positive quotient action still uses the constructed regular operator. -/
theorem positiveHalfAction_generator (n : ℕ → ℤ) (i : ℕ) :
    GenericTensor.positiveHalfAction orthogonalEven n
      (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      GenericTensor.positive orthogonalEven n i :=
  GenericTensor.positiveHalfAction_θ orthogonalEven n i

/-- Vacuum recovery for the two actual quotient half-actions and generated inputs. -/
theorem halfActions_generated (n : ℕ → ℤ) :
    GenericTensor.negativeHalfAction orthogonalEven generatedLeft
      (GenericTensor.positiveHalfAction orthogonalEven n generatedRight
        ((1 : H) ⊗ₜ[Coefficients.Ring] 1)) =
      generatedLeft ⊗ₜ[Coefficients.Ring] generatedRight :=
  GenericTensor.halfActions_vacuum orthogonalEven n generatedLeft generatedRight

end OddMath.CoveringQuantum.UDot.TriangularOperatorExamples

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Fixed-column residuals with infinitely many non-bar-consistent colours

The algebraic fixed-column reduction underlying Clark IV's bilinear-form comparison
is evaluated on two mixed generated inputs in the original modified algebra. The
source assumes finite, bar-consistent data; the propagated algebraic proof does not.
The convention remains v=q^-1 and rho=tau1-prime, with native cross Delta1/Delta2,
not an identification with the printed tau1/Delta3/Delta4 pairing. A single polynomial
is chosen before the dominant tensor weights and both coproducts. No nonzero tensor,
nonzero form, global joint convergence or nondegeneracy assertion is made.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.MixedResidualInfiniteExamples
open Coefficients GenericVerma GenericVerma.MixedGram VermaWeightExamples
open PolarizationTransport NormalizedMixedComparison PositiveComparison

/-- The ambient colours are infinite and the datum is not bar-consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- A fixed external column, before any tensor weights are chosen. -/
def rightWeight : ℕ →₀ ℤ := Finsupp.single 0 (-3)

/-- An upward generator followed by a downward generator. -/
def leftInput : modified datum Coefficients.q pi :=
  algebraWord datum rightWeight [(true, 0), (false, 0)]

/-- The reversed mixed word in the same original right column. -/
def rightInput : modified datum Coefficients.q pi :=
  algebraWord datum rightWeight [(false, 0), (true, 0)]

/-- Right-column support for the first actual generated input. -/
theorem left_column : leftInput * weightOne datum rightWeight = leftInput :=
  algebraWord_mul_one datum rightWeight [(true, 0), (false, 0)]

/-- Right-column support for the second actual generated input. -/
theorem right_column : rightInput * weightOne datum rightWeight = rightInput :=
  algebraWord_mul_one datum rightWeight [(false, 0), (true, 0)]

/-- The first concrete highest weight is dominant at every colour. -/
theorem zero_dominant : ∀ i, 0 ≤ datum.h i (0 : ℕ →₀ ℤ) := by
  intro i
  simp [RootDatum.h]

/-- The second concrete highest weight is dominant at every colour. -/
theorem single_dominant : ∀ i, 0 ≤ datum.h i (Finsupp.single 0 3) := by
  intro i
  simp only [datum, RootDatum.h, Finsupp.lapply_apply, Finsupp.single_apply]
  split_ifs <;> norm_num

/-- The explicit dominant weights have exactly the prescribed fixed difference. -/
theorem tensor_difference : (0 : ℕ →₀ ℤ) - Finsupp.single 0 3 = rightWeight := by
  simp [rightWeight, ← Finsupp.single_neg]

/-- One zero-constant polynomial works for all dominant weights with fixed difference
and, in particular, for both coproducts at the explicit dominant pair. -/
theorem mixed_residual :
    ∃ p : MvPolynomial ℕ Coefficients.Ring,
      MvPolynomial.constantCoeff p = 0 ∧
      (∀ (Λ Μ : ℕ →₀ ℤ) (hΛ : ∀ i, 0 ≤ datum.h i Λ)
        (hΜ : ∀ i, 0 ≤ datum.h i Μ) (s : Bool), Λ - Μ = rightWeight →
        modifiedGram datum Λ Μ hΛ hΜ s leftInput rightInput -
          GenericTensor.positiveModifiedForm datum leftInput rightInput =
            MvPolynomial.eval (deformationParameter datum Μ) p) ∧
      (modifiedGram datum 0 (Finsupp.single 0 3) zero_dominant single_dominant false
        leftInput rightInput - GenericTensor.positiveModifiedForm datum leftInput rightInput =
          MvPolynomial.eval (deformationParameter datum (Finsupp.single 0 3)) p) ∧
      (modifiedGram datum 0 (Finsupp.single 0 3) zero_dominant single_dominant true
        leftInput rightInput - GenericTensor.positiveModifiedForm datum leftInput rightInput =
          MvPolynomial.eval (deformationParameter datum (Finsupp.single 0 3)) p) := by
  obtain ⟨p, hp, h⟩ := fixed_column_residual datum rightWeight leftInput rightInput
    left_column right_column
  exact ⟨p, hp, h,
    h 0 (Finsupp.single 0 3) zero_dominant single_dominant false tensor_difference,
    h 0 (Finsupp.single 0 3) zero_dominant single_dominant true tensor_difference⟩

end OddMath.CoveringQuantum.UDot.MixedResidualInfiniteExamples

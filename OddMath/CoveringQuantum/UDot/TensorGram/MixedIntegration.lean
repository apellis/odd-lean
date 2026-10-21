/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.PositiveComparison
import OddMath.CoveringQuantum.UDot.TensorGram.Reduction

/-!
# Fixed-column normalized mixed tensor Gram comparison

For arbitrary finite mixed inputs in one right column, a single zero-constant
residual polynomial is chosen before the dominant weights and coproduct choice.
This is an algebraic comparison, not a separation or nondegeneracy theorem.
The fixed-column reduction underlying Clark IV's bilinear-form comparison
propagates without its ambient finiteness and bar-consistency assumptions;
the dominant weights and their fixed difference are retained explicitly.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.PositiveComparison
open Coefficients PreF GenericVerma MixedGram PolarizationTransport
open TensorPositive Reciprocal NormalizedMixedComparison ToralCancellation
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- The original algebra word is exactly the existing positive half word. -/
theorem algebraWord_pos_eq (ζ : X) (w : List I) :
    algebraWord D ζ (pos w) = word D true w ζ := by
  apply Subtype.ext
  induction w with
  | nil => rfl
  | cons i w ih =>
    change halfGen D Coefficients.q pi true i (ζ + shift D (pos w)) *
      (algebraWord D ζ (pos w)).val =
      halfGen D Coefficients.q pi true i (ζ + halfWeight D true (wordWeight w)) *
      halfWord D Coefficients.q pi true w ζ
    rw [shift_pos, ih]
    rfl

/-- The fixed normalized residual applies directly to the half words used
by the fixed-column reduction, not a replacement representation. -/
theorem halfWord_residual (Λ Μ : X)
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    modifiedGram D Λ Μ hΛ hΜ s (word D true u (Λ - Μ)) (word D true v (Λ - Μ)) -
      D.form Coefficients.q pi (monomial Coefficients.Ring u) (monomial Coefficients.Ring v) =
    MvPolynomial.eval (deformationParameter D Μ) (reciprocalError D u v) := by
  rw [← algebraWord_pos_eq, ← algebraWord_pos_eq]
  exact positive_residual_eq_eval D Λ Μ hΛ hΜ s u v

/-- Every actual fixed-column mixed pair has a SINGLE finite residual
polynomial, chosen before the growing highest weights and the coproduct.
This is a polynomial comparison, not a joint-limit or cofinality assertion. -/
theorem fixed_column_residual (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) :
    ∃ p : MvPolynomial I Coefficients.Ring,
      MvPolynomial.constantCoeff p = 0 ∧
      ∀ (Λ Μ : X) (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool),
        Λ - Μ = ζ →
        modifiedGram D Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D x y =
          MvPolynomial.eval (deformationParameter D Μ) p := by
  classical
  obtain ⟨c, hc⟩ := residual_sum D ζ x y hx hy
  refine ⟨c.sum (fun w a ↦ MvPolynomial.C a * reciprocalError D w.1 w.2), ?_, ?_⟩
  · simp [Finsupp.sum, map_sum, reciprocalError_constantCoeff]
  · intro Λ Μ hΛ hΜ s hζ
    rw [hc Λ Μ hΛ hΜ s]
    simp only [Finsupp.sum, map_sum, map_mul, MvPolynomial.eval_C]
    apply Finset.sum_congr rfl
    intro w hw
    rw [← hζ, halfWord_residual]

end OddMath.CoveringQuantum.UDot.PositiveComparison

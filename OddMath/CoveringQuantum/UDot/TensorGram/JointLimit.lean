/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration
import OddMath.CoveringQuantum.UDot.VermaLimit

/-!
# Uniform q-adic bounds for normalized mixed tensor Grams

Coefficient orders are measured after pi=+1 and pi=-1 specialization at q=0
(source v=q^-1). One explicit threshold bounds both specializations and both
native coproducts. No valuation on the covering ring with zero divisors,
positive-coroot weight, or nondegeneracy is assumed for this bound.
-/

noncomputable section
open scoped Topology
open Filter
namespace OddMath.CoveringQuantum.UDot.NormalizedJointLimit
open Coefficients PreF GenericVerma MixedGram PolarizationTransport PositiveComparison
open NormalizedMixedComparison
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- The residual depends on the fixed inputs and column, not on Λ, Μ or s. -/
def residualPolynomial (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) :
    MvPolynomial I Coefficients.Ring :=
  (fixed_column_residual D hD ζ x y hx hy).choose

theorem residualPolynomial_constantCoeff (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) :
    MvPolynomial.constantCoeff (residualPolynomial D hD ζ x y hx hy) = 0 :=
  (fixed_column_residual D hD ζ x y hx hy).choose_spec.1

theorem residualPolynomial_eval (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y)
    (Λ Μ : X) (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (hζ : Λ - Μ = ζ) :
    modifiedGram D hD Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D hD x y =
      MvPolynomial.eval (deformationParameter D Μ) (residualPolynomial D hD ζ x y hx hy) :=
  (fixed_column_residual D hD ζ x y hx hy).choose_spec.2 Λ Μ hΛ hΜ s hζ

/-- Explicit finite-coefficient threshold, including all negative orders.
The empty support has floor zero and is covered without a nonzero assumption. -/
def threshold (p : MvPolynomial I Coefficients.Ring)
    (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (N : ℤ) : ℤ :=
  max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom p)

/-- The maximum of the two explicit specialization thresholds. -/
def bothThreshold (p : MvPolynomial I Coefficients.Ring) (N : ℤ) : ℤ :=
  max (threshold p 1 (one_pow 2) N) (threshold p (-1) (by norm_num) N)

omit [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I] in
theorem bothThreshold_nonneg (p : MvPolynomial I Coefficients.Ring) (N : ℤ) :
    0 ≤ bothThreshold p N :=
  (le_max_left 0 _).trans (le_max_left _ _)

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- Evaluation estimate for the actual deformation parameters, not assumed convergence. -/
theorem polynomial_order (p : MvPolynomial I Coefficients.Ring)
    (hp : MvPolynomial.constantCoeff p = 0)
    (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (N : ℤ) (Μ : X)
    (hΜ : ∀ i ∈ p.vars, threshold p ε hε N ≤ D.h i Μ) :
    (N : WithTop ℤ) ≤ QAdic.order
      (specialize ε hε (MvPolynomial.eval (deformationParameter D Μ) p)) := by
  change (N : WithTop ℤ) ≤ QAdic.order ((specialize ε hε).toRingHom
    (MvPolynomial.eval (deformationParameter D Μ) p))
  rw [MvPolynomial.eval₂_comp]
  apply QAdic.eval_order_lower _ _ hp
  intro i hi
  change (threshold p ε hε N : WithTop ℤ) ≤
    QAdic.order (specialize ε hε (deformationParameter D Μ i))
  rw [deformationParameter_order]
  have hd : (1 : ℤ) ≤ D.d i := by exact_mod_cast D.d_pos i
  have hb : 0 ≤ threshold p ε hε N := le_max_left _ _
  have hh := hΜ i hi
  exact_mod_cast (show threshold p ε hε N ≤ (D.d i : ℤ) * (2 * D.h i Μ) by nlinarith)

/-- Direct bound on every actual dominant fixed-difference pair. There is no
positive-weight hypothesis, coefficient homogeneity, or weight-dependent floor. -/
theorem modifiedGram_order (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y)
    (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (N : ℤ)
    (Λ Μ : X) (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (hζ : Λ - Μ = ζ)
    (hbound : ∀ i ∈ (residualPolynomial D hD ζ x y hx hy).vars,
      threshold (residualPolynomial D hD ζ x y hx hy) ε hε N ≤ D.h i Μ) :
    (N : WithTop ℤ) ≤ QAdic.order (specialize ε hε
      (modifiedGram D hD Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D hD x y)) := by
  rw [residualPolynomial_eval D hD ζ x y hx hy Λ Μ hΛ hΜ s hζ]
  exact polynomial_order D _ (residualPolynomial_constantCoeff D hD ζ x y hx hy)
    ε hε N Μ hbound

/-- ONE explicit bound, chosen before the weights and coproduct, works for
both specializations and BOTH native coproducts simultaneously. -/
theorem modifiedGram_order_both (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) (N : ℤ) :
    let B := bothThreshold (residualPolynomial D hD ζ x y hx hy) N
    0 ≤ B ∧ ∀ (Λ Μ : X) (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ),
      Λ - Μ = ζ → (∀ i, B ≤ D.h i Μ) → ∀ s : Bool,
      (N : WithTop ℤ) ≤ QAdic.order (specialize 1 (one_pow 2)
        (modifiedGram D hD Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D hD x y)) ∧
      (N : WithTop ℤ) ≤ QAdic.order (specialize (-1) (by norm_num)
        (modifiedGram D hD Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D hD x y)) := by
  refine ⟨bothThreshold_nonneg _ _, ?_⟩
  intro Λ Μ hΛ hΜ hζ hb s
  constructor
  · exact modifiedGram_order D hD ζ x y hx hy 1 (one_pow 2) N Λ Μ hΛ hΜ s hζ
      (fun i _ ↦ (le_max_left _ _).trans (hb i))
  · exact modifiedGram_order D hD ζ x y hx hy (-1) (by norm_num) N Λ Μ hΛ hΜ s hζ
      (fun i _ ↦ (le_max_right _ _).trans (hb i))

end OddMath.CoveringQuantum.UDot.NormalizedJointLimit

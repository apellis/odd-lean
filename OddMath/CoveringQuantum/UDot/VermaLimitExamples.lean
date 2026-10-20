/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaLimit
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Finite-support Verma order bounds on infinite non-bar data

For the countable datum `VermaWeightExamples.datum`, `finite_support_order_both`
constructs a finitely supported weight meeting every variable bound of the exact
error polynomial for two inhomogeneous free inputs. One input has a coefficient
of q-order -3. The same weight gives the requested order at both pi specializations.
This exercises `normalizedPolarization_order`, needed by the mixed tensor comparison,
without assuming a large weight or using convergence along a possibly bottom filter.
The separately instantiated convergence statement makes no filter-nonvacuity claim.
-/

noncomputable section
open scoped Topology
namespace OddMath.CoveringQuantum.UDot.VermaLimitExamples
open PreF Coefficients GenericVerma VermaWeightExamples

/-- The datum has infinitely many colours and is not bar-consistent. -/
theorem applicability : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨inferInstance, not_barConsistent⟩

/-- A coefficient of negative q-order in the generic covering ring. -/
def coefficient : Coefficients.Ring :=
  algebraMap (RatFunc ℚ) Coefficients.Ring (RatFunc.X ^ (-3 : ℤ))

/-- Neither pi specialization makes this coefficient integral at q = 0. -/
theorem coefficient_order (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) :
    QAdic.order (specialize ε hε coefficient) = (-3 : ℤ) := by
  rw [coefficient, AlgHom.commutes]
  exact QAdic.order_X_zpow (-3)

/-- A finite free input with a negative-order scalar and two word lengths. -/
def leftInput : PreF Coefficients.Ring ℕ :=
  coefficient • θ Coefficients.Ring 0 + monomial Coefficients.Ring [0, 1]

/-- A second inhomogeneous finite free input, including the vacuum. -/
def rightInput : PreF Coefficients.Ring ℕ :=
  θ Coefficients.Ring 0 + monomial Coefficients.Ring [0, 1] +
    (Coefficients.q : Coefficients.Ring) • 1

/-- The maximum of the actual coefficient-floor thresholds at pi = +1 and -1. -/
def commonThreshold (N : ℤ) : ℤ :=
  max (comparisonThreshold datum 1 (one_pow 2) leftInput rightInput N)
    (comparisonThreshold datum (-1) (by norm_num) leftInput rightInput N)

/-- Only variables occurring in the exact error polynomial receive a coordinate. -/
def approximationWeight (N : ℤ) : ℕ →₀ ℤ :=
  ∑ i ∈ (freeComparisonError datum rightInput leftInput).vars,
    Finsupp.single i (commonThreshold N)

/-- The constructed weight meets every finite polynomial-variable bound exactly. -/
theorem approximationWeight_coordinate (N : ℤ) (i : ℕ)
    (hi : i ∈ (freeComparisonError datum rightInput leftInput).vars) :
    datum.h i (approximationWeight N) = commonThreshold N := by
  change (approximationWeight N) i = commonThreshold N
  simp [approximationWeight, Finsupp.single_apply, hi]

/-- Both specialized errors have the requested order at an explicitly constructed weight.
No global coordinate-filter nonvacuity or large-weight hypothesis is used. -/
theorem finite_support_order_both (N : ℤ) :
    (N : WithTop ℤ) ≤ QAdic.order (specialize 1 (one_pow 2)
      (normalizedPolarization datum (approximationWeight N) leftInput rightInput -
        datum.form Coefficients.q pi leftInput rightInput)) ∧
    (N : WithTop ℤ) ≤ QAdic.order (specialize (-1) (by norm_num)
      (normalizedPolarization datum (approximationWeight N) leftInput rightInput -
        datum.form Coefficients.q pi leftInput rightInput)) := by
  constructor
  · apply normalizedPolarization_order datum 1 (one_pow 2)
    intro i hi
    rw [approximationWeight_coordinate N i hi]
    exact le_max_left _ _
  · apply normalizedPolarization_order datum (-1) (by norm_num)
    intro i hi
    rw [approximationWeight_coordinate N i hi]
    exact le_max_right _ _

/-- The error remains exactly the evaluation of the original finite polynomial. -/
theorem normalized_difference (N : ℤ) :
    normalizedPolarization datum (approximationWeight N) leftInput rightInput -
      datum.form Coefficients.q pi leftInput rightInput =
    MvPolynomial.eval (deformationParameter datum (approximationWeight N))
      (freeComparisonError datum rightInput leftInput) :=
  normalizedPolarization_sub_half datum (approximationWeight N) leftInput rightInput

/-- The original conditional convergence statement also specializes to this datum.
Its filter nonvacuity is separate: this is not evidence for approximation, which
is instead supplied by the explicit weights in `finite_support_order_both`. -/
theorem conditional_tendsto (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) :
    Filter.Tendsto
      (fun Λ => specialize ε hε (normalizedPolarization datum Λ leftInput rightInput))
      (coordinateFilter datum)
      (𝓝 (specialize ε hε (datum.form Coefficients.q pi leftInput rightInput))) :=
  normalizedPolarization_tendsto datum ε hε leftInput rightInput

end OddMath.CoveringQuantum.UDot.VermaLimitExamples

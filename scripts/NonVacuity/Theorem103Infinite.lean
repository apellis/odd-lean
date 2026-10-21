import OddMath

/-! Non-vacuity checks in `NonVacuity.Theorem103Infinite`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Theorem103Infinite

open OddMath.CoveringQuantum.UDot.VermaWeightExamples
open OddMath.SKM.Theorem103InfiniteExamples

example : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent := infinite_nonbar
example (ε : Bool) (ζ μ : ℕ →₀ ℤ) := graphical ε ζ μ
example (ε : Bool) := negative_weight_graphical ε
example := unequal_weight_zero true
example := unequal_weight_zero false
example (μ : ℕ →₀ ℤ) (z : ℤ) := both_signs true μ z
example (μ : ℕ →₀ ℤ) (z : ℤ) := both_signs false μ z
example (μ : ℕ →₀ ℤ) := populated true μ
example (μ : ℕ →₀ ℤ) := populated false μ

end NonVacuity.Theorem103Infinite

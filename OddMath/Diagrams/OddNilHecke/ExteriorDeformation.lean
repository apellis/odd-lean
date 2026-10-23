/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# A two-strand odd nilHecke model with an exterior parameter

The matrices below satisfy the two-strand odd nilHecke relations together with an
odd square-zero parameter `δ` and the deformed cyclotomic relation `x₁² + x₁δ = 0`.
Over the dual numbers, `δ` acts nontrivially. Thus this cyclotomic relation does not
force the exterior parameter to vanish when the second strand is added.

This is a local test for the independent odd bubble coefficients in the
Nondegeneracy Conjecture of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §8. It is not a 2-representation: no cups, caps, Frobenius
functional or inversion matrices are constructed here.

The coefficient matrix is diagonal with entries `θ` and `-θ`, rather than the
scalar matrix `θ • 1`. This sign is necessary for supercentrality on the basis
with one even and one odd vector.
-/

namespace OddMath.OddNilHecke.ExteriorDeformation

variable {R : Type*} [CommRing R]

/-- The first odd dot on the ordered basis `(1, x₁)`. -/
def firstDot (θ : R) : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, -θ]

/-- The second odd dot. -/
def secondDot (θ : R) : Matrix (Fin 2) (Fin 2) R := !![θ, 0; 1, 0]

/-- The odd divided difference. -/
def crossing : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- Left multiplication by the odd exterior parameter. -/
def exterior (θ : R) : Matrix (Fin 2) (Fin 2) R := !![θ, 0; 0, -θ]

/-- The two-strand odd nilHecke relations hold in this model. -/
theorem nilHecke_relations (θ : R) :
    crossing (R := R) * crossing = 0 ∧
    firstDot θ * secondDot θ + secondDot θ * firstDot θ = 0 ∧
    crossing * firstDot θ + secondDot θ * crossing = 1 ∧
    firstDot θ * crossing + crossing * secondDot θ = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [crossing, firstDot, secondDot, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exterior parameter anticommutes with all odd generators. -/
theorem exterior_anticommutes (θ : R) (hθ : θ * θ = 0) :
    exterior θ * firstDot θ + firstDot θ * exterior θ = 0 ∧
    exterior θ * secondDot θ + secondDot θ * exterior θ = 0 ∧
    exterior θ * crossing + crossing * exterior θ = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [exterior, crossing, firstDot, secondDot, hθ]

/-- The exterior scalar is square zero. -/
theorem exterior_square (θ : R) (hθ : θ * θ = 0) :
    exterior θ * exterior θ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exterior, Matrix.mul_apply, Fin.sum_univ_two, hθ]

/-- The cyclotomic polynomial is `x₁(x₁ + δ)`, not `x₁²`. -/
theorem cyclotomic_relation (θ : R) (hθ : θ * θ = 0) :
    firstDot θ * firstDot θ + firstDot θ * exterior θ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exterior, firstDot, hθ]

/-- The exterior parameter is not lost in the matrix model. -/
theorem exterior_injective : Function.Injective (exterior (R := R)) := by
  intro θ η h
  exact congrArg (fun M => M 0 0) h

/-- Nonzero parameters act nontrivially. -/
theorem exterior_ne_zero {θ : R} (hθ : θ ≠ 0) : exterior θ ≠ 0 := by
  intro h
  exact hθ (congrArg (fun M => M 0 0) h)

/-- The parameter of the dual numbers, with nonzero square-zero coefficient. -/
def dualParameter : TrivSqZeroExt ℚ ℚ := TrivSqZeroExt.inr 1

/-- The dual-number instance has a genuinely nonzero exterior scalar and satisfies
all the local relations, including the deformed cyclotomic equation. -/
theorem dualNumber_model :
    exterior dualParameter ≠ 0 ∧
    exterior dualParameter * exterior dualParameter = 0 ∧
    firstDot dualParameter * firstDot dualParameter +
      firstDot dualParameter * exterior dualParameter = 0 := by
  have hs : dualParameter * dualParameter = 0 := by
    exact TrivSqZeroExt.inr_mul_inr ℚ 1 1
  refine ⟨exterior_ne_zero ?_, exterior_square _ hs, cyclotomic_relation _ hs⟩
  intro h
  have := congrArg TrivSqZeroExt.snd h
  norm_num [dualParameter] at this

end OddMath.OddNilHecke.ExteriorDeformation

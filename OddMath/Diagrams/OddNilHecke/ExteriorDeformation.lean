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

The cyclotomic polynomial is the specialization `n = 2`, `χ₁ = 0`, `d = -δ`
of Ebert–Lauda–Vera, *Derived superequivalences for spin symmetric groups and
odd sl₂-categorifications*, arXiv:2203.14153v2, Definition 3.9 and (3.26).
That source works over a field; the local matrix identities here hold over
every commutative ring.

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

/-- The exterior parameter anticommutes with all odd generators. -/
theorem exterior_anticommutes (θ : R) (hθ : θ * θ = 0) :
    exterior θ * firstDot θ + firstDot θ * exterior θ = 0 ∧
    exterior θ * secondDot θ + secondDot θ * exterior θ = 0 ∧
    exterior θ * crossing + crossing * exterior θ = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [exterior, crossing, firstDot, secondDot, hθ]

/-- The parameter of the dual numbers, with nonzero square-zero coefficient. -/
def dualParameter : TrivSqZeroExt ℚ ℚ := TrivSqZeroExt.inr 1

end OddMath.OddNilHecke.ExteriorDeformation

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Signed right multipliers and the mixed quadratic sign

For odd `u`, signed right multiplication on a regular supermodule is
`h ↦ σ(h) * u`, where `σ` is the parity involution. Its square is minus
right multiplication by `u²`. In particular, negating both crossings does
not repair a mixed odd/odd quadratic relation with nonzero constant term.

The rational four-dimensional example is the regular module of two-by-two
matrices, with even diagonal word idempotents and odd off-diagonal crossings.
Taking both dots zero gives the two-distinct-colour, zero-edge, cutoff-one
quadratic block. It isolates the mixed quadratic sign; it is not an action
of the entire quiver Hecke category. No projectivity or
cyclotomic action is asserted here.
-/
namespace OddMath.QuiverHecke.CyclotomicAction

variable {A : Type*} [Ring A]

/-- Signed right multiplication by an odd homogeneous element. -/
def oddRight (σ : A →+* A) (u h : A) : A := σ h * u

/-- The super-opposite sign for two odd right multipliers, including their order. -/
theorem oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    oddRight σ u (oddRight σ v h) = -(h * (v * u)) := by
  simp only [oddRight, map_mul, hσ h, hv, mul_neg, neg_mul, mul_assoc]

/-- A simultaneous minus on both odd crossings leaves the quadratic sign unchanged. -/
theorem neg_oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    -oddRight σ u (-oddRight σ v h) = -(h * (v * u)) := by
  simpa only [oddRight, map_neg, neg_mul, neg_neg] using oddRight_comp σ hσ u v hv h

/-- The two word idempotents are the diagonal matrix units. -/
abbrev TwoWordAlgebra := Matrix (Fin 2) (Fin 2) ℚ

def parityMatrix : TwoWordAlgebra := !![1, 0; 0, -1]

end OddMath.QuiverHecke.CyclotomicAction

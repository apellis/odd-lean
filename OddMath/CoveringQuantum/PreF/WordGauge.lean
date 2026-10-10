import OddMath.CoveringQuantum.PreF.Basic
import LieLean.Algebra.QuantumGroup.GabberKac.MapCoeffs
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Diagonal changes of the word basis

A unit-valued function on pairs of simple indices gives a diagonal linear
isomorphism of the free algebra. The coefficient of a word is the product over
ordered pairs of positions. This is the word-level map needed for the covering
twisting comparison; no descent to a Serre quotient is asserted here.

The word basis is reused from the pinned LieLean dependency.
-/

noncomputable section

namespace OddMath.CoveringQuantum.PreF

variable {k I : Type*} [CommRing k] (f : I → I → kˣ)

/-- The phase of a word: multiply `f(i,j)` over positions with `i` preceding `j`. -/
def wordPhase : List I → kˣ
  | [] => 1
  | i :: w => (w.map (f i)).prod * wordPhase w

@[simp] theorem wordPhase_nil : wordPhase f [] = 1 := rfl

@[simp] theorem wordPhase_cons (i : I) (w : List I) :
    wordPhase f (i :: w) = (w.map (f i)).prod * wordPhase f w := rfl

/-- The invertible diagonal change of the free-algebra word basis. -/
def wordGauge : PreF k I ≃ₗ[k] PreF k I :=
  (FreeAlgebra.wordBasis k I).equiv
    ((FreeAlgebra.wordBasis k I).unitsSMul (wordPhase f)) (Equiv.refl _)

/-- The diagonal change has the specified phase on each monomial. -/
theorem wordGauge_monomial (w : List I) :
    wordGauge f (monomial k w) = (wordPhase f w : k) • monomial k w := by
  have h := (FreeAlgebra.wordBasis k I).equiv_apply w
    ((FreeAlgebra.wordBasis k I).unitsSMul (wordPhase f)) (Equiv.refl _)
  simpa only [wordGauge, FreeAlgebra.wordBasis_apply, Module.Basis.unitsSMul_apply,
    Equiv.refl_apply, Units.smul_def, monomial] using h

/-- The inverse change multiplies each word by the inverse phase. -/
theorem wordGauge_symm_monomial (w : List I) :
    (wordGauge f).symm (monomial k w) = ((wordPhase f w)⁻¹ : kˣ) • monomial k w := by
  apply (wordGauge f).injective
  rw [LinearEquiv.apply_symm_apply, Units.smul_def, map_smul, wordGauge_monomial, smul_smul]
  simp

@[simp] theorem wordGauge_one : wordGauge f 1 = 1 := by
  simpa using wordGauge_monomial f []

@[simp] theorem wordGauge_theta (i : I) : wordGauge f (θ k i) = θ k i := by
  simpa [wordPhase, monomial] using wordGauge_monomial f [i]

/-- Concatenation separates into the two internal phases and the cross-term. -/
theorem wordPhase_append (u v : List I) :
    wordPhase f (u ++ v) = wordPhase f u * wordPhase f v *
      (u.map fun i ↦ (v.map (f i)).prod).prod := by
  induction u with
  | nil => simp
  | cons i u ih =>
    simp only [List.cons_append, wordPhase_cons, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, ih]
    ac_rfl

end OddMath.CoveringQuantum.PreF

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.UniversalPolynomialParameters
import OddMath.SKM.SeparatingFields
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Reduced rational normalization parameters

The reducedness step of `docs/Nondegeneracy/GroundRingDescent.md` §4,
supporting the proposed ground-ring deduction for Brundan–Ellis §8.
The inversion pairing has positive-definite coefficient at zero over ℚ.
Applying it twice to a square-zero element proves reducedness for every
abelian group, including torsion groups. Polynomial reducedness then applies
to the exact allowed slots and unsaturated normalization group of §3.
No domain, finiteness or independent-root hypothesis is imposed.
This does not prove injection of the integral parameter ring or nondegeneracy.
-/

noncomputable section
namespace OddMath.SKM.UniversalCoefficientReduced

variable {G : Type*} [AddCommGroup G]

/-- Invert each group label, leaving its rational coefficient unchanged. -/
def inversion : AddMonoidAlgebra ℚ G ≃+* AddMonoidAlgebra ℚ G :=
  AddMonoidAlgebra.mapDomainRingEquiv ℚ
    { toFun := fun g => -g
      invFun := fun g => -g
      left_inv := neg_neg
      right_inv := neg_neg
      map_add' := neg_add }

@[simp] theorem coeff_inversion (f : AddMonoidAlgebra ℚ G) (g : G) :
    (inversion f).coeff g = f.coeff (-g) := by
  simp [inversion]

@[simp] theorem inversion_inversion (f : AddMonoidAlgebra ℚ G) :
    inversion (inversion f) = f := by
  ext g
  simp

/-- The coefficient at zero of the inversion pairing is a sum of squares. -/
theorem coeff_mul_inversion (f : AddMonoidAlgebra ℚ G) :
    (f * inversion f).coeff 0 = ∑ g ∈ f.coeff.support, f.coeff g ^ 2 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp [Finsupp.sum, pow_two]

/-- Positivity over ℚ detects zero without a torsion-free group hypothesis. -/
theorem eq_zero_of_mul_inversion_eq_zero (f : AddMonoidAlgebra ℚ G)
    (h : f * inversion f = 0) : f = 0 := by
  have hs : ∑ g ∈ f.coeff.support, f.coeff g ^ 2 = 0 := by
    rw [← coeff_mul_inversion, h]
    rfl
  have hc := (Finset.sum_sq_eq_zero_iff f.coeff.support f.coeff).mp hs
  ext g
  by_cases hg : g ∈ f.coeff.support
  · exact hc g hg
  · exact Finsupp.notMem_support_iff.mp hg

/-- Rational group algebras of arbitrary abelian groups have no nonzero nilpotents. -/
theorem rationalGroupAlgebra_isReduced (G : Type*) [AddCommGroup G] :
    IsReduced (AddMonoidAlgebra ℚ G) := by
  apply (isReduced_iff_pow_one_lt 2 (by decide)).mpr
  intro f hf
  apply eq_zero_of_mul_inversion_eq_zero
  apply eq_zero_of_mul_inversion_eq_zero
  calc
    (f * inversion f) * inversion (f * inversion f) =
        f ^ 2 * (inversion f) ^ 2 := by rw [map_mul, inversion_inversion]; ring
    _ = 0 := by rw [hf, zero_mul]

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- Reducedness of the polynomial ring on every allowed coefficient slot. -/
theorem rationalParameters_isReduced :
    IsReduced (MvPolynomial (UniversalPolynomialParameters.Slot D)
      (AddMonoidAlgebra ℚ (NormalizationParameterGroup.Group D))) := by
  let := rationalGroupAlgebra_isReduced (NormalizationParameterGroup.Group D)
  infer_instance

/-- The rational parameter ring is separated by its prime-quotient fraction fields. -/
theorem rationalParameters_separate
    (f : MvPolynomial (UniversalPolynomialParameters.Slot D)
      (AddMonoidAlgebra ℚ (NormalizationParameterGroup.Group D)))
    (h : ∀ p, primeFractionMap _ p f = 0) : f = 0 := by
  let := rationalParameters_isReduced D
  exact primeFractionMaps_separate _ f h

end OddMath.SKM.UniversalCoefficientReduced

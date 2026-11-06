import OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedPolynomial

/-! # The ordered three-dot correction with the original scalar parameters

Brundan--Ellis (1.9), repeated outer colour. Retain the source correction
as an ordered polynomial in three arbitrary endomorphisms, before any
selected module chart or weight evaluation is substituted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X)

/-- The ordered summand of the three-dot correction. -/
def tripleDotCorrectionSum {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (r s : ℕ) (d : k) (A B C : R) : R :=
  ∑ t ∈ Finset.range r, (SKM.zsign k (D.parity i * (D.parity j + t)) * d) •
    (C ^ (r - 1 - t) * B ^ s * A ^ t)

/-- The original Sc correction, with all three operator orders retained. -/
def tripleDotCorrectionPolynomial {R : Type*} [Ring R] [Algebra k R]
    (Sc : SKM.Scalars D k) (i j : I) (A B C : R) : R :=
  tripleDotCorrectionSum D i j (D.dn i j) 0 (Sc.t i j : k) A B C +
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      tripleDotCorrectionSum D i j r s (Sc.s i j r s) A B C

/-- Algebra maps preserve the ordered summand; no commutativity of the three operators is assumed. -/
theorem tripleDotCorrectionSum_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (φ : R →ₐ[k] S) (i j : I) (r s : ℕ) (d : k) (A B C : R) :
    φ (tripleDotCorrectionSum D i j r s d A B C) =
      tripleDotCorrectionSum D i j r s d (φ A) (φ B) (φ C) := by
  simp only [tripleDotCorrectionSum, map_sum, map_smul, map_mul, map_pow]

/-- Algebra maps retain the ORIGINAL Sc coefficients and all operator orders. -/
theorem tripleDotCorrectionPolynomial_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (Sc : SKM.Scalars D k) (φ : R →ₐ[k] S) (i j : I) (A B C : R) :
    φ (tripleDotCorrectionPolynomial D Sc i j A B C) =
      tripleDotCorrectionPolynomial D Sc i j (φ A) (φ B) (φ C) := by
  simp only [tripleDotCorrectionPolynomial, map_add, map_sum, tripleDotCorrectionSum_map]

/-- Exact binding to the checked canonical-content correction: the acting
scalars are parameterTwist Sc, while the polynomial coefficients are Sc. -/
theorem contentMixedBraidPolynomial_eq_ordered
    (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ) (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound (β + ([i,j,i] : Multiset I))) :
    contentMixedBraidPolynomial D Sc cutoff bound β i j M w =
      tripleDotCorrectionPolynomial D Sc i j
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (firstDot_parity D (parameterTwist D Sc) i [j,i]) M w)
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (contentTripleDot_one_parity D (parameterTwist D Sc) i j) M w)
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (contentTripleDot_two_parity D (parameterTwist D Sc) i j) M w) := by
  rfl

end OddMath.QuiverHecke.ELVOld

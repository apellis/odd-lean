/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.JointScalarDescent
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Ring.Prod

/-!
# Separating fields for reduced rational algebras

The prime-quotient fraction-field step of `docs/Nondegeneracy/GroundRingDescent.md` §4,
supporting Brundan–Ellis, *Super Kac–Moody 2-categories*, §8. For an arbitrary
reduced commutative rational algebra, the prime quotients yield a jointly
zero-reflecting family of characteristic-zero fields. No domain, finite-generation,
or nontriviality assumption is made on the source.
-/

noncomputable section
namespace OddMath.SKM

universe u
variable (A : Type u) [CommRing A] [Algebra ℚ A]

/-- The fraction field of a prime quotient of a rational algebra. -/
def primeFractionField (p : PrimeSpectrum A) : Type u := by
  letI : p.asIdeal.IsPrime := p.isPrime
  exact FractionRing (A ⧸ p.asIdeal)

instance (p : PrimeSpectrum A) : Field (primeFractionField A p) := by
  unfold primeFractionField
  letI : p.asIdeal.IsPrime := p.isPrime
  infer_instance

instance (p : PrimeSpectrum A) : CharZero (primeFractionField A p) := by
  unfold primeFractionField
  let : p.asIdeal.IsPrime := p.isPrime
  have : CharZero (A ⧸ p.asIdeal) := Algebra.charZero_of_charZero ℚ _
  infer_instance

/-- The quotient map followed by its injective map into the fraction field. -/
def primeFractionMap (p : PrimeSpectrum A) : A →+* primeFractionField A p := by
  letI : p.asIdeal.IsPrime := p.isPrime
  exact (algebraMap (A ⧸ p.asIdeal) (FractionRing (A ⧸ p.asIdeal))).comp
    (Ideal.Quotient.mk p.asIdeal)

omit [Algebra ℚ A] in
/-- Prime-quotient fraction fields jointly detect zero in a reduced algebra.
The indexing spectrum may be empty precisely when the source is trivial. -/
theorem primeFractionMaps_separate [IsReduced A] (a : A)
    (h : ∀ p : PrimeSpectrum A, primeFractionMap A p a = 0) : a = 0 := by
  have hp : ∀ J : Ideal A, J.IsPrime → a ∈ J := by
    intro J hJ
    let p : PrimeSpectrum A := ⟨J, hJ⟩
    let : J.IsPrime := hJ
    have hz := h p
    have hi : Function.Injective
        (algebraMap (A ⧸ J) (FractionRing (A ⧸ J))) :=
      IsFractionRing.injective _ _
    have hz' : (algebraMap (A ⧸ J) (FractionRing (A ⧸ J)))
        ((Ideal.Quotient.mk J) a) = 0 := by
      change ((algebraMap (A ⧸ J) (FractionRing (A ⧸ J))).comp
        (Ideal.Quotient.mk J)) a = 0
      exact hz
    have hq : (Ideal.Quotient.mk J) a = 0 := hi (by simpa using hz')
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hq
  exact isNilpotent_iff_eq_zero.mp (nilpotent_iff_mem_prime.mpr hp)

end OddMath.SKM

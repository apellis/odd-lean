/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQuotientPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The ELV content polynomial cokernel

The canonical enlarged cyclotomic quotient is the cokernel of the prescribed
injective P over the ordinary, possibly noncommutative ring B[s]. Its action
comes from right-appended old arrows and the moving dot/square, not from
transporting an action along the ground-ring cokernel equivalence. The ideal
sum proves exactness componentwise. This is the exact sequence needed by the
right-projectivity argument; finite projectivity is not asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- A row of the enlarged cyclotomic quotient, with all old source words. -/
abbrev QuotientRow (i : I) (ν w : List I) :=
  OddMath.FiniteHomMatrix.RightModule (contentObject D Sc cutoff ν)
    (quotientPresheaf D Sc cutoff i w)

/-- All enlarged target words and old source words of the fixed content. -/
abbrev QuotientContent (i : I) (ν : List I) :=
  ∀ w : ContentWords (i :: ν), QuotientRow D Sc cutoff i ν w.val

def quotientRowCentral (i : I) (ν w : List I) :
    QuotientRow D Sc cutoff i ν w →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      QuotientRow D Sc cutoff i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (quotientCentralNat D Sc cutoff i w)

def quotientContentCentral (i : I) (ν : List I) :
    QuotientContent D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      QuotientContent D Sc cutoff i ν :=
  LinearMap.pi fun w => (quotientRowCentral D Sc cutoff i ν w.val).comp (LinearMap.proj w)

/-- The full enlarged cyclotomic quotient as an ordinary right B[s]-module. -/
abbrev QuotientPolynomial (i : I) (ν : List I) :=
  CyclotomicAction.RightCentralPolynomialModule (quotientContentCentral D Sc cutoff i ν)

/-- The canonical map on a full content row. -/
def canonicalAppendRow (i : I) (ν w : List I) :
    AppendRow D Sc cutoff i ν w →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      QuotientRow D Sc cutoff i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (canonicalAppendNat D Sc cutoff i w)

def canonicalAppendContent (i : I) (ν : List I) :
    AppendContent D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      QuotientContent D Sc cutoff i ν :=
  LinearMap.pi fun w => (canonicalAppendRow D Sc cutoff i ν w.val).comp (LinearMap.proj w)

/-- The prescribed quotient map respects the old algebra and central variable. -/
def canonicalAppendPolynomial (i : I) (ν : List I) :
    K0 D Sc cutoff i ν →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      QuotientPolynomial D Sc cutoff i ν :=
  CyclotomicAction.RightCentralPolynomialModule.map _ _
    (canonicalAppendContent D Sc cutoff i ν) (by
      intro z
      funext w v
      exact canonicalAppendTarget_central D Sc cutoff i v.val w.val (z w v))

@[simp] theorem canonicalAppendPolynomial_apply (i : I) (ν : List I)
    (z : K0 D Sc cutoff i ν) (w : ContentWords (i :: ν)) (v : ContentWords ν) :
    canonicalAppendPolynomial D Sc cutoff i ν z w v =
      canonicalAppendTarget D Sc cutoff i v.val w.val (z w v) := rfl

/-- The old matrix action retains every off-diagonal old arrow. -/
theorem quotientContent_smul_apply (i : I) (ν : List I)
    (b : (ContentRing D Sc cutoff ν)ᵐᵒᵖ) (z : QuotientContent D Sc cutoff i ν)
    (w : ContentWords (i :: ν)) (v : ContentWords ν) :
    (b • z) w v = ∑ t : ContentWords ν,
      quotientPull D Sc cutoff i v.val t.val w.val (b.unop (t, v)) (z w t) := rfl

/-- The central polynomial variable is the moving dot or square in each quotient. -/
theorem quotientPolynomial_X (i : I) (ν : List I) (z : QuotientContent D Sc cutoff i ν) :
    MulOpposite.op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν)) •
      CyclotomicAction.RightCentralPolynomialModule.of (quotientContentCentral D Sc cutoff i ν) z =
    CyclotomicAction.RightCentralPolynomialModule.of _ (quotientContentCentral D Sc cutoff i ν z) :=
  CyclotomicAction.RightCentralPolynomialModule.X_smul_of _ z

/-- Surjectivity is the componentwise canonical quotient, including empty content. -/
theorem canonicalAppendPolynomial_surjective (i : I) (ν : List I) :
    Function.Surjective (canonicalAppendPolynomial D Sc cutoff i ν) := by
  intro z
  choose a ha using fun (w : ContentWords (i :: ν)) (v : ContentWords ν) =>
    canonicalAppendTarget_surjective D Sc cutoff i v.val w.val (z w v)
  exact ⟨a, funext fun w => funext fun v => ha w v⟩

/-- IS2 identifies the kernel with the image of the prescribed twisted P. -/
theorem ker_canonicalAppendPolynomial (i : I) (ν : List I) :
    LinearMap.ker (canonicalAppendPolynomial D Sc cutoff i ν) =
      LinearMap.range (pPolynomial D Sc cutoff i ν) := by
  ext z
  constructor
  · intro hz
    have hz' : canonicalAppendPolynomial D Sc cutoff i ν z = 0 := hz
    have h (w : ContentWords (i :: ν)) (v : ContentWords ν) :
        z w v ∈ LinearMap.range (pMap D Sc cutoff i v.val w.val) := by
      rw [← ker_canonicalAppendTarget]
      exact congrFun (congrFun hz' w) v
    choose a ha using h
    exact ⟨a, funext fun w => funext fun v => ha w v⟩
  · rintro ⟨a, rfl⟩
    change canonicalAppendPolynomial D Sc cutoff i ν (pPolynomial D Sc cutoff i ν a) = 0
    funext w v
    exact (show pMap D Sc cutoff i v.val w.val (a w v) ∈
        LinearMap.ker (canonicalAppendTarget D Sc cutoff i v.val w.val) from by
      rw [ker_canonicalAppendTarget]
      exact ⟨a w v, rfl⟩)

/-- Polynomial-module cokernel identification with the enlarged cyclotomic quotient. -/
def pPolynomialCokernelEquiv (i : I) (ν : List I) :
    (K0 D Sc cutoff i ν ⧸ LinearMap.range (pPolynomial D Sc cutoff i ν)) ≃ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] QuotientPolynomial D Sc cutoff i ν :=
  (Submodule.quotEquivOfEq _ _ (ker_canonicalAppendPolynomial D Sc cutoff i ν).symm).trans
    ((canonicalAppendPolynomial D Sc cutoff i ν).quotKerEquivOfSurjective
      (canonicalAppendPolynomial_surjective D Sc cutoff i ν))

@[simp] theorem pPolynomialCokernelEquiv_mk (i : I) (ν : List I) (z : K0 D Sc cutoff i ν) :
    pPolynomialCokernelEquiv D Sc cutoff i ν (Submodule.Quotient.mk z) =
      canonicalAppendPolynomial D Sc cutoff i ν z := rfl

/-- The literal content sequence K₁ → K₀ → F over the ordinary right polynomial ring. -/
def contentShortComplex (i : I) (ν : List I) :
    ShortComplex (ModuleCat (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ) :=
  ShortComplex.moduleCatMkOfKerLERange
    (ModuleCat.ofHom (pPolynomial D Sc cutoff i ν))
    (ModuleCat.ofHom (canonicalAppendPolynomial D Sc cutoff i ν))
    (by
      change LinearMap.range (pPolynomial D Sc cutoff i ν) ≤
        LinearMap.ker (canonicalAppendPolynomial D Sc cutoff i ν)
      rw [ker_canonicalAppendPolynomial])

/-- The canonical sequence 0 → K₁ → K₀ → F → 0 is short exact. -/
theorem contentShortComplex_shortExact (i : I) (ν : List I) :
    (contentShortComplex D Sc cutoff i ν).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    (ker_canonicalAppendPolynomial D Sc cutoff i ν).symm
  mono_f := (ModuleCat.mono_iff_injective _).mpr (pPolynomial_injective D Sc cutoff i ν)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (canonicalAppendPolynomial_surjective D Sc cutoff i ν)

end OddMath.QuiverHecke.ELVOld

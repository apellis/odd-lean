/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialRows

/-! # Polynomial rows as old-word idempotent summands

The concrete row insertion identifies the finite polynomial row module with
finite families in the right ideals `e(t) B[s]`. This uses the old-word matrix
idempotents themselves and allows zero corners and empty content.
-/

noncomputable section
open CategoryTheory MulOpposite
open scoped Classical DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The constant polynomial old-word idempotent, in the right-module scalar ring. -/
def oldPolynomialIdempotent (ν : List I) (t : ContentWords ν) :
    (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ :=
  op (Polynomial.C (FiniteHomMatrix.idem (obj := contentObject D Sc cutoff ν) t))

@[simp] theorem oldRowInsert_unit (ν : List I) (t : ContentWords ν) :
    oldRowInsert D Sc cutoff ν t (oldRowUnit D Sc cutoff ν t) =
      FiniteHomMatrix.idem (obj := contentObject D Sc cutoff ν) t := by
  exact oldRowInsert_single D Sc cutoff ν t t _

/-- The split projection is coordinatewise multiplication by the old-word idempotent. -/
theorem polynomialRowsSection_retraction (ν : List I) (d : ℕ)
    (f : SourcePolynomialFree D Sc cutoff ν d) (q : SourcePolynomialIndex ν d) :
    polynomialRowsSection D Sc cutoff ν d (polynomialRowsRetraction D Sc cutoff ν d f) q =
      f q * oldPolynomialIdempotent D Sc cutoff ν q.1.1 := by
  simp only [polynomialRowsRetraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.toSpanSingleton_apply, map_sum, map_smul]
  change (∑ r : SourcePolynomialIndex ν d, f r •
    polynomialRowsSection D Sc cutoff ν d
      (CyclotomicAction.RightCentralPolynomialModule.of _
        (DirectSum.of _ (r, 0) (oldRowUnit D Sc cutoff ν r.1.1)))) q = _
  have hs (r : SourcePolynomialIndex ν d) :
      polynomialRowsSection D Sc cutoff ν d
        (CyclotomicAction.RightCentralPolynomialModule.of _
          (DirectSum.of _ (r, 0) (oldRowUnit D Sc cutoff ν r.1.1))) =
        Pi.single r (oldPolynomialIdempotent D Sc cutoff ν r.1.1) := by
    rw [polynomialRowsSection_of D Sc cutoff ν d (r, 0)]
    simp only [oldRowInsert_unit, Polynomial.monomial_zero_left, oldPolynomialIdempotent]
  simp only [hs, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (Ne.symm hb)]
  · simp

/-- Finite families of polynomial rows fixed by their old-word idempotents.
In the original (non-opposite) ring these are precisely the right ideals `e(t) B[s]`. -/
def PolynomialIdempotentRows (ν : List I) (d : ℕ) :
    Submodule (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourcePolynomialFree D Sc cutoff ν d) where
  carrier := {f | ∀ q, f q * oldPolynomialIdempotent D Sc cutoff ν q.1.1 = f q}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg q; simp [add_mul, hf q, hg q]
  smul_mem' := by
    intro a f hf q
    change (a * f q) * _ = a * f q
    rw [mul_assoc, hf q]

/-- The image of the concrete row insertion is exactly the idempotent summands. -/
theorem polynomialRowsSection_mem_iff (ν : List I) (d : ℕ)
    (f : SourcePolynomialFree D Sc cutoff ν d) :
    f ∈ (polynomialRowsSection D Sc cutoff ν d).range ↔
      ∀ q, f q * oldPolynomialIdempotent D Sc cutoff ν q.1.1 = f q := by
  constructor
  · rintro ⟨z, rfl⟩ q
    rw [← polynomialRowsSection_retraction, polynomialRowsRetraction_section]
  · intro h
    refine ⟨polynomialRowsRetraction D Sc cutoff ν d f, ?_⟩
    funext q
    rw [polynomialRowsSection_retraction, h q]

/-- Polynomial-linear identification with the finite family of old-word idempotent ideals. -/
def polynomialRowsIdempotentEquiv (ν : List I) (d : ℕ) :
    PolynomialOldRows D Sc cutoff ν d ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialIdempotentRows D Sc cutoff ν d where
  toFun z := ⟨polynomialRowsSection D Sc cutoff ν d z,
    (polynomialRowsSection_mem_iff D Sc cutoff ν d _).mp ⟨z, rfl⟩⟩
  invFun f := polynomialRowsRetraction D Sc cutoff ν d f.val
  left_inv := polynomialRowsRetraction_section D Sc cutoff ν d
  right_inv f := by
    apply Subtype.ext
    funext q
    exact (polynomialRowsSection_retraction D Sc cutoff ν d f.val q).trans (f.property q)
  map_add' x y := by apply Subtype.ext; exact map_add _ x y
  map_smul' a z := by apply Subtype.ext; exact map_smul _ a z

/-- The defining fixed-point condition is literally membership in `e(t) B[s]`,
with multiplication in the original content ring, not its opposite. -/
theorem polynomialIdempotentRows_mem_iff (ν : List I) (d : ℕ)
    (f : SourcePolynomialFree D Sc cutoff ν d) :
    f ∈ PolynomialIdempotentRows D Sc cutoff ν d ↔
      ∀ q, ∃ b : Polynomial (ContentRing D Sc cutoff ν),
        (f q).unop =
          Polynomial.C (FiniteHomMatrix.idem (obj := contentObject D Sc cutoff ν) q.1.1) * b := by
  constructor
  · intro hf q
    refine ⟨(f q).unop, ?_⟩
    exact (congrArg MulOpposite.unop (hf q)).symm
  · intro hf q
    apply MulOpposite.unop_injective
    change Polynomial.C (FiniteHomMatrix.idem (obj := contentObject D Sc cutoff ν) q.1.1) *
      (f q).unop = (f q).unop
    obtain ⟨b, hb⟩ := hf q
    rw [hb, ← mul_assoc, ← Polynomial.C_mul, FiniteHomMatrix.idem_sq]

end OddMath.QuiverHecke.ELVOld

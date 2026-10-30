/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendPolynomialRows

/-! # Append polynomial rows as literal old-idempotent ideals

The split row insertion has image exactly the finite family of right ideals
`e(t) B[s]`, with the full noncommutative content ring and all zero corners retained.
-/
noncomputable section
open CategoryTheory MulOpposite
open scoped Classical DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The split projection is coordinatewise multiplication by the old-word idempotent. -/
theorem appendPolynomialRowsSection_retraction (i : I) (ν : List I) (d : ℕ)
    (f : AppendPolynomialFree D Sc cutoff i ν d) (q : AppendPolynomialIndex i ν d) :
    appendPolynomialRowsSection D Sc cutoff i ν d (appendPolynomialRowsRetraction D Sc cutoff i ν d f) q =
      f q * oldPolynomialIdempotent D Sc cutoff ν q.1.1 := by
  simp only [appendPolynomialRowsRetraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.toSpanSingleton_apply, map_sum, map_smul]
  change (∑ r : AppendPolynomialIndex i ν d, f r •
    appendPolynomialRowsSection D Sc cutoff i ν d
      (CyclotomicAction.RightCentralPolynomialModule.of _
        (DirectSum.of _ (r, 0) (oldRowUnit D Sc cutoff ν r.1.1)))) q = _
  have hs (r : AppendPolynomialIndex i ν d) :
      appendPolynomialRowsSection D Sc cutoff i ν d
        (CyclotomicAction.RightCentralPolynomialModule.of _
          (DirectSum.of _ (r, 0) (oldRowUnit D Sc cutoff ν r.1.1))) =
        Pi.single r (oldPolynomialIdempotent D Sc cutoff ν r.1.1) := by
    rw [appendPolynomialRowsSection_of D Sc cutoff i ν d (r, 0)]
    simp only [oldRowInsert_unit, Polynomial.monomial_zero_left, oldPolynomialIdempotent]
  simp only [hs, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (Ne.symm hb)]
  · simp

/-- Finite families of polynomial rows fixed by their old-word idempotents.
In the original (non-opposite) ring these are precisely the right ideals `e(t) B[s]`. -/
def AppendPolynomialIdempotentRows (i : I) (ν : List I) (d : ℕ) :
    Submodule (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendPolynomialFree D Sc cutoff i ν d) where
  carrier := {f | ∀ q, f q * oldPolynomialIdempotent D Sc cutoff ν q.1.1 = f q}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg q; simp [add_mul, hf q, hg q]
  smul_mem' := by
    intro a f hf q
    change (a * f q) * _ = a * f q
    rw [mul_assoc, hf q]

/-- The image of the concrete row insertion is exactly the idempotent summands. -/
theorem appendPolynomialRowsSection_mem_iff (i : I) (ν : List I) (d : ℕ)
    (f : AppendPolynomialFree D Sc cutoff i ν d) :
    f ∈ (appendPolynomialRowsSection D Sc cutoff i ν d).range ↔
      ∀ q, f q * oldPolynomialIdempotent D Sc cutoff ν q.1.1 = f q := by
  constructor
  · rintro ⟨z, rfl⟩ q
    rw [← appendPolynomialRowsSection_retraction, appendPolynomialRowsRetraction_section]
  · intro h
    refine ⟨appendPolynomialRowsRetraction D Sc cutoff i ν d f, ?_⟩
    funext q
    rw [appendPolynomialRowsSection_retraction, h q]

/-- Polynomial-linear identification with the finite family of old-word idempotent ideals. -/
def appendPolynomialRowsIdempotentEquiv (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialOldRows D Sc cutoff i ν d ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialIdempotentRows D Sc cutoff i ν d where
  toFun z := ⟨appendPolynomialRowsSection D Sc cutoff i ν d z,
    (appendPolynomialRowsSection_mem_iff D Sc cutoff i ν d _).mp ⟨z, rfl⟩⟩
  invFun f := appendPolynomialRowsRetraction D Sc cutoff i ν d f.val
  left_inv := appendPolynomialRowsRetraction_section D Sc cutoff i ν d
  right_inv f := by
    apply Subtype.ext
    funext q
    exact (appendPolynomialRowsSection_retraction D Sc cutoff i ν d f.val q).trans (f.property q)
  map_add' x y := by apply Subtype.ext; exact map_add _ x y
  map_smul' a z := by apply Subtype.ext; exact map_smul _ a z

/-- The defining fixed-point condition is literally membership in `e(t) B[s]`,
with multiplication in the original content ring, not its opposite. -/
theorem appendPolynomialIdempotentRows_mem_iff (i : I) (ν : List I) (d : ℕ)
    (f : AppendPolynomialFree D Sc cutoff i ν d) :
    f ∈ AppendPolynomialIdempotentRows D Sc cutoff i ν d ↔
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

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.PositiveWordCoefficients

/-!
# Adjoint Laurent coefficients

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 2: upward-generator
adjointness for the existing modified form and its formal Laurent coefficient
shift, for arbitrary colours without bar consistency. The reversed-word
append formula is not identified with physical left-cons evaluation.
-/

noncomputable section
open scoped LaurentSeries
namespace OddMath.CoveringQuantum

/-- Expansion of an integral power of the unit q, without extending bar. -/
theorem signLaurent_qp (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    signLaurent σ hσ (UDot.qp Coefficients.q z) =
      (HahnSeries.single z 1 : LaurentSeries ℚ) := by
  change ((Units.map (signLaurent σ hσ).toMonoidHom (Coefficients.q ^ z) :
    (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  change (signLaurent σ hσ (Coefficients.q : Coefficients.Ring)) ^ z = _
  rw [signLaurent_q, ← RatFunc.single_zpow]

namespace UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- The upward adjoint formula in the existing modified algebra. The generator's
right weight is ν, not the common column's right weight μ. This identity holds
for arbitrary modified elements; no weight or graphical premise is needed. -/
theorem sesquilinearForm_E_adjoint (i : I) (ν : X)
    (x y : modified D Coefficients.q pi) :
    sesquilinearForm D
      (⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ * x) y =
    qp Coefficients.q (-(D.d i * (1 + D.h i ν))) *
      sesquilinearForm D x
        (⟨F D Coefficients.q pi i (ν + D.α i),
          F_mem_modified D Coefficients.q pi i (ν + D.α i)⟩ * y) := by
  rw [sesquilinearForm_adjoint]
  have hs : starModified D
      ⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ =
      qp Coefficients.q (-(D.d i * (1 + D.h i ν))) •
        (⟨F D Coefficients.q pi i (ν + D.α i),
          F_mem_modified D Coefficients.q pi i (ν + D.α i)⟩ :
          modified D Coefficients.q pi) := by
    apply Subtype.ext
    change (star D Coefficients.q pi bar barData (E D Coefficients.q pi i ν)).unop =
      qp Coefficients.q (-(D.d i * (1 + D.h i ν))) •
        F D Coefficients.q pi i (ν + D.α i)
    simpa only [add_comm] using (star_E (D := D) barData i ν)
  rw [hs, smul_mul_assoc, map_smul, smul_eq_mul]

/-- The bent form is q^δ times the old form; there is no π factor for E. -/
theorem sesquilinearForm_E_bent (i : I) (ν : X)
    (x y : modified D Coefficients.q pi) :
    sesquilinearForm D x
      (⟨F D Coefficients.q pi i (ν + D.α i),
        F_mem_modified D Coefficients.q pi i (ν + D.α i)⟩ * y) =
    qp Coefficients.q (D.d i * (1 + D.h i ν)) *
      sesquilinearForm D
        (⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ * x) y := by
  rw [sesquilinearForm_E_adjoint, ← mul_assoc, qp_mul, add_neg_cancel, qp_zero, one_mul]

/-- BE2 Theorem 10.3 Claim 2, algebraic coefficient step only. Specialize π
only after evaluating the existing form, without finite-colour or bar restrictions.
No assumption on grades, graphical normalization, or form identities is used. -/
theorem sesquilinearForm_E_bent_coeff (σ : ℚ) (hσ : σ ^ 2 = 1)
    (i : I) (ν : X) (x y : modified D Coefficients.q pi) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm D x
      (⟨F D Coefficients.q pi i (ν + D.α i),
        F_mem_modified D Coefficients.q pi i (ν + D.α i)⟩ * y))).coeff z =
    (signLaurent σ hσ (sesquilinearForm D
      (⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ * x) y)).coeff
        (z - D.d i * (1 + D.h i ν)) := by
  rw [sesquilinearForm_E_bent, map_mul, signLaurent_qp,
    HahnSeries.coeff_single_mul, one_mul]

/-- With the existing reversed-word convention, algebraic left multiplication
adds a letter at the END of the list being reversed, not at its beginning. -/
theorem positiveHalf_reverse_append (i : I) (μ : X) (a : List I) :
    (⟨E D Coefficients.q pi i
        (μ + halfWeight D true (wordWeight a.reverse)),
      E_mem_modified D Coefficients.q pi i
        (μ + halfWeight D true (wordWeight a.reverse))⟩ : modified D Coefficients.q pi) *
      positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a.reverse)) =
    positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (a ++ [i]).reverse)) := by
  apply Subtype.ext
  change E D Coefficients.q pi i _ * halfMap D Coefficients.q pi true μ _ =
    halfMap D Coefficients.q pi true μ _
  simp only [halfMap_monomial, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, halfWord, halfGen, ite_true]

/-- Reversed-word consumer of the coefficient step, with the weight of the
suffix computed by the existing half-word API. The second argument is arbitrary. -/
theorem sesquilinearForm_E_reversed_coeff (σ : ℚ) (hσ : σ ^ 2 = 1)
    (i : I) (μ : X) (a : List I) (y : modified D Coefficients.q pi) (z : ℤ) :
    let ν := μ + halfWeight D true (wordWeight a.reverse)
    (signLaurent σ hσ (sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a.reverse)))
      (⟨F D Coefficients.q pi i (ν + D.α i),
        F_mem_modified D Coefficients.q pi i (ν + D.α i)⟩ * y))).coeff z =
    (signLaurent σ hσ (sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (a ++ [i]).reverse)))
      y)).coeff (z - D.d i * (1 + D.h i ν)) := by
  dsimp only
  rw [sesquilinearForm_E_bent_coeff, positiveHalf_reverse_append]

end UDot.GenericTensor
end OddMath.CoveringQuantum

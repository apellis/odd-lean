/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.Coefficients.Splitting
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Nondegeneracy over the generic covering coefficients from the two specializations

The generic covering coefficient ring `ℚ(q)[π]/(π² - 1)` of Brundan–Ellis, arXiv:1701.04133v2,
§9, splits as `ℚ(q) × ℚ(q)` through the specializations `π ↦ 1` and `π ↦ -1`
(`Coefficients.splitEquiv`). Accordingly a bilinear form over the covering ring has trivial left
radical as soon as both of its specializations do. The proof uses the idempotents `(1 ± π)/2`.
This serves the nondegeneracy statement of Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1.

## Main definitions

* `Coefficients.signIdempotent ε`: the idempotent `(1 + επ)/2`.

## Main results

* `Coefficients.leftRadical_trivial_of_specialize`: if the base changes of a bilinear form along
  `specialize 1` and `specialize (-1)` have trivial left radical, so does the form.
-/

noncomputable section

namespace OddMath.CoveringQuantum.Coefficients

open TensorProduct

/-- An element `e` with `σ(r c) e = r σ(c) e` for an additive section `σ : K → R` of the
scalar map kills every `x` with `1 ⊗ x = 0` in `K ⊗[R] M`. -/
theorem smul_eq_zero_of_one_tmul_eq_zero {R K M : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [AddCommGroup M] [Module R M] (σ : K →+ R) (e : R)
    (hσ : ∀ r c, σ (algebraMap R K r * c) * e = r * σ c * e) (h1 : σ 1 * e = e) {x : M}
    (hx : (1 : K) ⊗ₜ[R] x = 0) : e • x = 0 := by
  let φ : K →ₗ[R] M →ₗ[R] M := LinearMap.mk₂ R (fun c m ↦ (σ c * e) • m)
    (fun c c' m ↦ by rw [map_add, add_mul, add_smul])
    (fun r c m ↦ by rw [Algebra.smul_def, hσ, mul_assoc, mul_smul])
    (fun c m m' ↦ smul_add _ m m')
    (fun r c m ↦ smul_comm _ r m)
  have h := congrArg (TensorProduct.lift φ) hx
  rwa [TensorProduct.lift.tmul, map_zero, LinearMap.mk₂_apply, h1] at h

/-- The idempotent `(1 + επ)/2` of the covering ring. -/
def signIdempotent (ε : RatFunc ℚ) : Ring :=
  algebraMap (RatFunc ℚ) Ring 2⁻¹ * (1 + algebraMap (RatFunc ℚ) Ring ε * pi)

theorem signIdempotent_add : signIdempotent 1 + signIdempotent (-1) = 1 := by
  rw [signIdempotent, signIdempotent, ← mul_add, map_one, map_neg, map_one]
  rw [show (1 + 1 * pi) + (1 + -1 * pi) = algebraMap (RatFunc ℚ) Ring 2 by
    rw [map_ofNat]; ring, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]

theorem pi_mul_signIdempotent (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) :
    pi * signIdempotent ε = algebraMap (RatFunc ℚ) Ring ε * signIdempotent ε := by
  have h : algebraMap (RatFunc ℚ) Ring ε ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  rw [signIdempotent]
  linear_combination (algebraMap (RatFunc ℚ) Ring 2⁻¹ * algebraMap (RatFunc ℚ) Ring ε) * pi_sq -
    (algebraMap (RatFunc ℚ) Ring 2⁻¹ * pi) * h

/-- On `(1 + επ)/2`, every coefficient acts through its specialization at `π = ε`. -/
theorem specialize_mul_signIdempotent (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (r : Ring) :
    algebraMap (RatFunc ℚ) Ring (specialize ε hε r) * signIdempotent ε = r * signIdempotent ε := by
  have hr : r ∈ Algebra.adjoin (RatFunc ℚ) {pi} := by
    rw [pi, AdjoinRoot.adjoinRoot_eq_top]; trivial
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, specialize_pi, pi_mul_signIdempotent ε hε]
  | algebraMap a => rw [AlgHom.commutes]; rfl
  | add x y _ _ hx hy => rw [map_add, map_add, add_mul, add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, mul_assoc, hy, mul_left_comm, hx, mul_assoc]
    exact mul_left_comm y x _

/-- If `1 ⊗ x = 0` after specializing at `π = ε`, then `(1 + επ)/2 • x = 0`. -/
theorem signIdempotent_smul_eq_zero {M : Type*} [AddCommGroup M] [Module Ring M] (ε : RatFunc ℚ)
    (hε : ε ^ 2 = 1) {x : M}
    (hx : letI := (specialize ε hε).toRingHom.toAlgebra; (1 : RatFunc ℚ) ⊗ₜ[Ring] x = 0) :
    signIdempotent ε • x = 0 := by
  let _ := (specialize ε hε).toRingHom.toAlgebra
  refine smul_eq_zero_of_one_tmul_eq_zero (algebraMap (RatFunc ℚ) Ring).toAddMonoidHom _
    (fun r c ↦ ?_) (by simp) hx
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul]
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    mul_comm _ (algebraMap _ _ c),
    mul_assoc, specialize_mul_signIdempotent]
  ring

/-- A bilinear form over the generic covering ring has trivial left radical when both of its
specializations `π ↦ 1` and `π ↦ -1` (extensions of scalars to `ℚ(q)`) do. -/
theorem leftRadical_trivial_of_specialize {M : Type*} [AddCommGroup M] [Module Ring M]
    (B : LinearMap.BilinForm Ring M)
    (h₁ : letI := (specialize 1 (one_pow 2)).toRingHom.toAlgebra;
      ∀ t : RatFunc ℚ ⊗[Ring] M, (∀ s, B.baseChange (RatFunc ℚ) t s = 0) → t = 0)
    (h₂ : letI := (specialize (-1) (by norm_num)).toRingHom.toAlgebra;
      ∀ t : RatFunc ℚ ⊗[Ring] M, (∀ s, B.baseChange (RatFunc ℚ) t s = 0) → t = 0) :
    ∀ x : M, (∀ y, B x y = 0) → x = 0 := by
  intro x hx
  have key (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
      (h : letI := (specialize ε hε).toRingHom.toAlgebra;
        ∀ t : RatFunc ℚ ⊗[Ring] M, (∀ s, B.baseChange (RatFunc ℚ) t s = 0) → t = 0) :
      signIdempotent ε • x = 0 := by
    let _ := (specialize ε hε).toRingHom.toAlgebra
    refine signIdempotent_smul_eq_zero ε hε (h _ fun s ↦ ?_)
    induction s with
    | tmul c y => rw [LinearMap.BilinForm.baseChange_tmul, hx, zero_smul]
    | add s t hs ht => rw [map_add, hs, ht, add_zero]
  rw [← one_smul Ring x, ← signIdempotent_add, add_smul, key 1 (one_pow 2) h₁,
    key (-1) (by norm_num) h₂, add_zero]

end OddMath.CoveringQuantum.Coefficients

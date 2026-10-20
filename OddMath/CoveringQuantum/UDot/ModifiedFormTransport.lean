/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ModifiedFormUniqueness

/-!
# Rank-one tests of modified-form convention transport

The negative-normalized `modifiedForm` must not be identified with the bilinear
precursor in Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1 or its following
remark. At weight zero, the actual commutator and rho-adjointness force
`B(F_i, F_i) = π_i * B(E_i, E_i)`. Thus the negative-normalized form has positive
norm `π_i * norm_i`, not `norm_i`.

Both natural candidate transports are defined with the original maps. The direct
psi pullback fails positive normalization for an odd root; the sigma/psi pullback
has the correct generator norm but fails the original star-adjoint identity.
These are convention diagnostics, not a counterexample to Theorem 10.1 and not a
construction of its form. They identify why a different precursor is necessary.

The universal norm comparison needs neither finiteness nor bar consistency.
The diagnostics for `modifiedForm` hold over the generic covering ring with
arbitrary colours; neither bar consistency nor root independence is assumed.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

private abbrev e (i : I) (μ : X) := positiveHalf D Coefficients.q pi μ
  (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))
private abbrev f (i : I) (μ : X) := negativeHalf D Coefficients.q pi μ
  (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))
private abbrev o (μ : X) := positiveHalf D Coefficients.q pi μ 1

private theorem rho_e_zero (i : I) :
    rhoModified D Coefficients.q pi pi_sq (e D i 0) =
      qp Coefficients.q (-(D.d i : ℤ)) • f D i (D.α i) := by
  apply Subtype.ext
  simp [e, f, rho_E]

private theorem rho_f_zero (i : I) :
    rhoModified D Coefficients.q pi pi_sq (f D i 0) =
      qp Coefficients.q (-(D.d i : ℤ)) • e D i (-D.α i) := by
  apply Subtype.ext
  simp [e, f, rho_F]

private theorem ef_zero (i : I) :
    e D i (-D.α i) * f D i 0 = D.pii pi i • (f D i (D.α i) * e D i 0) := by
  apply Subtype.ext
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (D.parity i) with h | h <;> simp [h]
  have h := comm_rel D Coefficients.q pi i i 0
  simpa [e, f, hp, SuperCartanDatum.pii, sub_eq_zero] using h

/-- At weight zero, rho-adjointness forces a parity factor between the two generator norms. -/
theorem rho_adjoint_generator_zero
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
    (hadj : ∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y))
    (i : I) : B (negativeHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) (negativeHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) = D.pii pi i * B (positiveHalf D
        Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) := by
  have he : e D i 0 * o D 0 = e D i 0 := by
    apply Subtype.ext
    simpa [e, o] using E_mul_one_self D Coefficients.q pi i 0
  have hf : f D i 0 * o D 0 = f D i 0 := by
    apply Subtype.ext
    simpa [f, o] using F_mul_one_self D Coefficients.q pi i 0
  have ha := hadj (e D i 0) (o D 0) (e D i 0)
  have hb := hadj (f D i 0) (o D 0) (f D i 0)
  rw [he, rho_e_zero, smul_mul_assoc, map_smul, smul_eq_mul] at ha
  rw [hf, rho_f_zero, smul_mul_assoc, ef_zero, smul_smul, map_smul, smul_eq_mul] at hb
  rw [ha, hb]
  ring

/-- Restriction of the original scalar-bar automorphism to the modified algebra. -/
def psiModified : modified D Coefficients.q pi →ₛₗ[bar] modified D Coefficients.q pi where
  toFun x := ⟨psi D Coefficients.q pi bar barData x,
    psi_mem_modified D Coefficients.q pi barData x.property⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (psi_smul barData c x.val)

/-- Restriction of the original star; no adjoint is chosen from a pairing. -/
def starModified : modified D Coefficients.q pi →ₛₗ[bar] modified D Coefficients.q pi :=
  (rhoModified D Coefficients.q pi pi_sq).comp (psiModified D)

@[simp] theorem coe_starModified (x : modified D Coefficients.q pi) :
    (starModified D x : CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      (star D Coefficients.q pi bar barData x).unop := rfl

private theorem psi_e (i : I) (μ : X) : psiModified D (e D i μ) = e D i μ := by
  apply Subtype.ext
  change psi D Coefficients.q pi bar barData _ = _
  simp [e]

private theorem psi_o (μ : X) : psiModified D (o D μ) = o D μ := by
  apply Subtype.ext
  change psi D Coefficients.q pi bar barData _ = _
  simp [o]

private theorem sigma_o (μ : X) : sigmaModified D Coefficients.q pi pi_sq (o D μ) = o D μ := by
  apply Subtype.ext
  simp [o]


/-- Direct psi pullback of the negative-normalized form. This is not BE2's normalized form. -/
def psiPullback : modified D Coefficients.q pi →ₛₗ[bar]
    (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring) :=
  LinearMap.comp (modifiedForm D) (psiModified D)

/-- The sigma/psi formula applied to the negative-normalized form, without identifying it
with Clark's precursor. The star-adjoint identity fails for an odd generator. -/
def sigmaPsiPullback : modified D Coefficients.q pi →ₛₗ[bar]
    (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring) :=
  ((modifiedForm D).compl₁₂ (sigmaModified D Coefficients.q pi pi_sq)
    (sigmaModified D Coefficients.q pi pi_sq)).comp (psiModified D)

/-- The negative-normalized form has a parity-twisted positive generator norm at zero. -/
theorem modifiedForm_positive_generator_zero (i : I) :
    modifiedForm D (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)))
      (positiveHalf D Coefficients.q pi 0
        (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) =
      D.pii pi i * D.norm Coefficients.q pi i := by
  have h := rho_adjoint_generator_zero D (modifiedForm D) (modifiedForm_adjoint D) i
  simp only [modifiedForm_negativeHalf, SuperCartanDatum.serreForm_θ_θ, ↓reduceIte] at h
  calc
    _ = (D.pii pi i) ^ 2 * modifiedForm D (e D i 0) (e D i 0) := by
      rw [D.pii_sq pi pi_sq, one_mul]
    _ = D.pii pi i * D.norm Coefficients.q pi i := by rw [h]; ring

/-- The covering parameter is not specialized to the even value. -/
theorem covering_pi_ne_one : pi ≠ (1 : Coefficients.Ring) := by
  intro h
  have he := congrArg (specialize (-1) (by norm_num)) h
  have : (-1 : RatFunc ℚ) = 1 := by simpa only [specialize_pi, map_one] using he
  norm_num at this

/-- An odd generator's positive norm differs from the half-algebra norm. -/
theorem modifiedForm_positive_generator_zero_ne (i : I) (hi : D.parity i = 1) :
    modifiedForm D (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) ≠ D.norm Coefficients.q pi i := by
  rw [modifiedForm_positive_generator_zero]
  have hp : D.pii pi i = pi := by
    simp only [SuperCartanDatum.pii, hi, show (1 : ZMod 2).val = 1 by decide, pow_one]
  rw [hp]
  intro h
  apply covering_pi_ne_one
  exact (norm_isUnit D.toSuperCartanDatum i).mul_right_cancel (h.trans (one_mul _).symm)

/-- The direct psi pullback still has the incorrect odd positive norm. -/
theorem psiPullback_positive_generator_zero_ne (i : I) (hi : D.parity i = 1) :
    psiPullback D (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) ≠ D.norm Coefficients.q pi i := by
  change modifiedForm D (psiModified D (e D i 0)) (e D i 0) ≠ _
  rw [psi_e]
  exact modifiedForm_positive_generator_zero_ne D i hi

/-- Sigma fixes the generator normalization, but this alone does not transport adjointness. -/
theorem sigmaPsiPullback_positive_generator_zero (i : I) :
    sigmaPsiPullback D (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) (positiveHalf D Coefficients.q pi 0
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) = D.norm Coefficients.q pi i := by
  have hs : sigmaModified D Coefficients.q pi pi_sq (e D i 0) = f D i (D.α i) := by
    apply Subtype.ext
    simp [e, f]
  change modifiedForm D (sigmaModified D Coefficients.q pi pi_sq (psiModified D (e D i 0)))
    (sigmaModified D Coefficients.q pi pi_sq (e D i 0)) = _
  rw [psi_e, hs, modifiedForm_negativeHalf, SuperCartanDatum.serreForm_θ_θ]
  simp

/-- The other side of the putative star-adjoint identity has the extra parity factor. -/
theorem sigmaPsiPullback_star_generator_zero (i : I) :
    sigmaPsiPullback D (positiveHalf D Coefficients.q pi 0 1)
      (starModified D (positiveHalf D Coefficients.q pi 0
        (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) *
        positiveHalf D Coefficients.q pi 0
          (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i))) =
      D.pii pi i * D.norm Coefficients.q pi i := by
  have hr : starModified D (e D i 0) = rhoModified D Coefficients.q pi pi_sq (e D i 0) := by
    change rhoModified D Coefficients.q pi pi_sq (psiModified D (e D i 0)) = _
    rw [psi_e]
  have hs : sigmaModified D Coefficients.q pi pi_sq
      (rhoModified D Coefficients.q pi pi_sq (e D i 0) * e D i 0) =
        rhoModified D Coefficients.q pi pi_sq (e D i 0) * e D i 0 := by
    apply Subtype.ext
    simp [e, rho_E]
  have he : e D i 0 * o D 0 = e D i 0 := by
    apply Subtype.ext
    simpa [e, o] using E_mul_one_self D Coefficients.q pi i 0
  change modifiedForm D (sigmaModified D Coefficients.q pi pi_sq (psiModified D (o D 0)))
    (sigmaModified D Coefficients.q pi pi_sq (starModified D (e D i 0) * e D i 0)) = _
  rw [psi_o, sigma_o, hr, hs, ← modifiedForm_adjoint, he, modifiedForm_positive_generator_zero]

/-- With an odd root, this sigma/psi pullback does not satisfy the original star-adjoint law. -/
theorem sigmaPsiPullback_not_star_adjoint (i : I) (hi : D.parity i = 1) :
    ¬ (∀ u x y, sigmaPsiPullback D (u * x) y =
      sigmaPsiPullback D x (starModified D u * y)) := by
  intro h
  have he : e D i 0 * o D 0 = e D i 0 := by
    apply Subtype.ext
    simpa [e, o] using E_mul_one_self D Coefficients.q pi i 0
  have hh := h (e D i 0) (o D 0) (e D i 0)
  rw [he, sigmaPsiPullback_positive_generator_zero, sigmaPsiPullback_star_generator_zero] at hh
  apply modifiedForm_positive_generator_zero_ne D i hi
  rw [modifiedForm_positive_generator_zero]
  exact hh.symm

end OddMath.CoveringQuantum.UDot.GenericTensor

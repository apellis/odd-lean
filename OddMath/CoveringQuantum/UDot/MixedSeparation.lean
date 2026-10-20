/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.SesquilinearForm

/-!
# Nondegeneracy on the first mixed plane

For each simple root, both the actual positive bilinear form and the BE2
sesquilinear form are nondegenerate on the submodule spanned by `1_{-αᵢ}` and
`qᵢ Fᵢ Eᵢ 1_{-αᵢ}`. This is a bounded mixed-coordinate contribution to the
nondegeneracy assertion of Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1.

Writing `c = (θᵢ, θᵢ)` and `m = qᵢ Fᵢ Eᵢ 1_{-αᵢ}`, subtracting `c 1_{-αᵢ}`
produces a vector orthogonal to the scalar coordinate, with norm `πᵢ qᵢ² c²`.
That norm is a unit in the generic covering ring, including both specializations
of π. Thus the mixed coefficient can be recovered even when it is a zero divisor.
The calculation uses the quotient commutator at weight zero and the positive-half
normalization, not an assumed detecting family or a canonical basis.

The form is available for arbitrary colours without bar consistency; root
independence is not required. This does not establish full-form nondegeneracy: arbitrary weights,
higher mixed degrees, and cancellation among general triangular tensors remain
outside the theorem.
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

/-- The first mixed adjoint product, at right weight minus the simple root. -/
def mixedGenerator (i : I) : modified D Coefficients.q pi :=
  rhoModified D Coefficients.q pi pi_sq (e D i (-D.α i)) * e D i (-D.α i)

omit [DecidableEq I] [DecidableEq X] in
private theorem parity_sq (i : I) : D.parity i * D.parity i = D.parity i := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (D.parity i) with h | h <;> simp [h]

private theorem rho_e_minus (i : I) :
    rhoModified D Coefficients.q pi pi_sq (e D i (-D.α i)) =
      qp Coefficients.q (D.d i) • f D i 0 := by
  apply Subtype.ext
  simp [e, f, rho_E, RootDatum.h_α, D.isGCM.diag]

private theorem rho_e_zero (i : I) :
    rhoModified D Coefficients.q pi pi_sq (e D i 0) =
      qp Coefficients.q (-(D.d i : ℤ)) • f D i (D.α i) := by
  apply Subtype.ext
  simp [e, f, rho_E]

private theorem ef_zero (i : I) :
    e D i (-D.α i) * f D i 0 = D.pii pi i • (f D i (D.α i) * e D i 0) := by
  apply Subtype.ext
  have h := comm_rel D Coefficients.q pi i i 0
  simpa [e, f, parity_sq, SuperCartanDatum.pii, sub_eq_zero] using h

private theorem e_unit (i : I) (μ : X) : e D i μ * o D μ = e D i μ := by
  apply Subtype.ext
  simpa [e, o] using E_mul_one_self D Coefficients.q pi i μ

private theorem positive_square (i : I) :
    e D i 0 * e D i (-D.α i) = positiveHalf D Coefficients.q pi (-D.α i)
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i * θ Coefficients.Ring i)) := by
  apply Subtype.ext
  change (e D i 0 : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
    (e D i (-D.α i) : CoveringUDot Coefficients.Ring D Coefficients.q pi) =
    halfMap D Coefficients.q pi true (-D.α i) _
  simp only [e, positiveHalf_θ]
  rw [show θ Coefficients.Ring i * θ Coefficients.Ring i = monomial Coefficients.Ring [i, i] by
    simp, halfMap_monomial]
  simp [halfWord, halfGen, halfRoot, E_mul_one_self]

omit [DecidableEq X] in
private theorem half_square_norm (i : I) :
    D.serreForm Coefficients.q pi pi_sq
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i * θ Coefficients.Ring i))
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i * θ Coefficients.Ring i)) =
        (1 + D.pii pi i * qp Coefficients.q (-(2 * (D.d i : ℤ)))) *
          (D.norm Coefficients.q pi i)^2 := by
  rw [SuperCartanDatum.serreForm_toSerreF]
  change PreF.form _ _ _ _ = _
  rw [form_mul_θ, rDeriv_mul_θ]
  simp [form_θ_θ, SuperCartanDatum.chi, SuperCartanDatum.dot_self,
    SuperCartanDatum.pii, parity_sq, qp]
  ring

private theorem mixed_unit (i : I) :
    positiveModifiedForm D (o D (-D.α i)) (mixedGenerator D i) = D.norm Coefficients.q pi i := by
  rw [mixedGenerator, ← positiveModifiedForm_adjoint, e_unit,
    positiveModifiedForm_positiveHalf, SuperCartanDatum.serreForm_θ_θ]
  simp

private theorem e_mixed (i : I) :
    e D i (-D.α i) * mixedGenerator D i =
      (D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ))) •
        (rhoModified D Coefficients.q pi pi_sq (e D i 0) *
          (e D i 0 * e D i (-D.α i))) := by
  rw [mixedGenerator, rho_e_minus, rho_e_zero]
  simp only [smul_mul_assoc, mul_smul_comm, ← mul_assoc, ef_zero, smul_smul]
  congr 1
  rw [mul_assoc, qp_mul]
  ring_nf

/-- The actual positive form has a nonzero mixed Gram pivot. -/
theorem positiveModifiedForm_mixedGenerator_self (i : I) :
    positiveModifiedForm D (mixedGenerator D i) (mixedGenerator D i) =
      (1 + D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ))) *
        (D.norm Coefficients.q pi i)^2 := by
  change positiveModifiedForm D
    (rhoModified D Coefficients.q pi pi_sq (e D i (-D.α i)) * e D i (-D.α i))
    (mixedGenerator D i) = _
  rw [positiveModifiedForm_adjoint, rhoModified_rhoModified, e_mixed,
    map_smul, smul_eq_mul, ← positiveModifiedForm_adjoint, positive_square,
    positiveModifiedForm_positiveHalf, half_square_norm]
  have hp := D.pii_sq pi pi_sq i
  have hq : qp Coefficients.q (2 * (D.d i : ℤ)) *
      qp Coefficients.q (-(2 * (D.d i : ℤ))) = 1 := by rw [qp_mul]; simp
  linear_combination (D.norm Coefficients.q pi i)^2 *
    (qp Coefficients.q (2 * (D.d i : ℤ)) * qp Coefficients.q (-(2 * (D.d i : ℤ))) * hp + hq)

/-- Subtract the scalar coordinate before detecting the mixed coordinate. -/
def mixedPivot (i : I) : modified D Coefficients.q pi :=
  mixedGenerator D i + (-D.norm Coefficients.q pi i) • o D (-D.α i)

/-- The first mixed two-coordinate submodule of the actual modified algebra. -/
def mixedPlane (i : I) : Submodule Coefficients.Ring (modified D Coefficients.q pi) :=
  Submodule.span Coefficients.Ring {o D (-D.α i), mixedGenerator D i}

@[simp] theorem positiveModifiedForm_unit_mixedPivot (i : I) :
    positiveModifiedForm D (o D (-D.α i)) (mixedPivot D i) = 0 := by
  rw [mixedPivot, map_add, map_smul, smul_eq_mul, mixed_unit,
    positiveModifiedForm_positiveHalf, SuperCartanDatum.serreForm_one_one, mul_one, add_neg_cancel]

/-- A unit Gram pivot over the covering ring, not merely a nonzero specialization. -/
theorem positiveModifiedForm_mixedPivot_self (i : I) :
    positiveModifiedForm D (mixedPivot D i) (mixedPivot D i) =
      D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ)) *
        (D.norm Coefficients.q pi i)^2 := by
  have hm := mixed_unit D i
  have hm' := (positiveModifiedForm_comm D (mixedGenerator D i) (o D (-D.α i))).trans hm
  simp only [mixedPivot, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    positiveModifiedForm_mixedGenerator_self,
    hm, hm', positiveModifiedForm_positiveHalf, SuperCartanDatum.serreForm_one_one]
  ring

omit [DecidableEq I] [DecidableEq X] in
private theorem pivot_isUnit (i : I) :
    IsUnit (D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ)) *
      (D.norm Coefficients.q pi i)^2) := by
  have hp : IsUnit (D.pii pi i) := isUnit_iff_exists_inv.mpr
    ⟨D.pii pi i, by simpa only [pow_two] using D.pii_sq pi pi_sq i⟩
  exact (hp.mul (Units.isUnit (Coefficients.q ^ (2 * (D.d i : ℤ))))).mul
    ((norm_isUnit D.toSuperCartanDatum i).pow 2)

/-- The mixed coordinate is recovered independently of the scalar coordinate. -/
theorem positiveModifiedForm_mixedPivot_detect (i : I) (a b : Coefficients.Ring) :
    positiveModifiedForm D (mixedPivot D i)
      (a • o D (-D.α i) + b • mixedGenerator D i) =
        b * (D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ)) *
          (D.norm Coefficients.q pi i)^2) := by
  have ho : positiveModifiedForm D (mixedPivot D i) (o D (-D.α i)) = 0 := by
    rw [positiveModifiedForm_comm, positiveModifiedForm_unit_mixedPivot]
  have hm : positiveModifiedForm D (mixedPivot D i) (mixedGenerator D i) =
      D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ)) * (D.norm Coefficients.q pi i)^2 := by
    have hh := positiveModifiedForm_mixedPivot_self D i
    change positiveModifiedForm D (mixedPivot D i)
      (mixedGenerator D i + (-D.norm Coefficients.q pi i) • o D (-D.α i)) = _ at hh
    simpa only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, ho, mul_zero,
      add_zero] using hh
  simp only [map_add, map_smul, smul_eq_mul, ho, hm, mul_zero, zero_add]

/-- Two actual pairings separate the scalar and mixed triangular coordinates. -/
theorem positiveModifiedForm_mixed_coordinates_eq_zero_iff (i : I) (a b : Coefficients.Ring) :
    (positiveModifiedForm D (o D (-D.α i))
        (a • o D (-D.α i) + b • mixedGenerator D i) = 0 ∧
      positiveModifiedForm D (mixedPivot D i)
        (a • o D (-D.α i) + b • mixedGenerator D i) = 0) ↔ a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨ha, hb⟩
    rw [positiveModifiedForm_mixedPivot_detect] at hb
    have hb' : b = 0 := (pivot_isUnit D i).mul_right_cancel (hb.trans (zero_mul _).symm)
    subst b
    simpa only [zero_smul, add_zero, map_smul, smul_eq_mul,
      positiveModifiedForm_positiveHalf, SuperCartanDatum.serreForm_one_one, mul_one,
      and_true] using ha
  · rintro ⟨rfl, rfl⟩
    simp

/-- The calculated mixed pivot is invertible in the unspecialized covering ring. -/
theorem positiveModifiedForm_mixedPivot_self_isUnit (i : I) :
    IsUnit (positiveModifiedForm D (mixedPivot D i) (mixedPivot D i)) := by
  rw [positiveModifiedForm_mixedPivot_self]
  exact pivot_isUnit D i

/-- These are genuinely two independent coordinates in the modified quotient. -/
theorem mixed_coordinates_eq_zero_iff (i : I) (a b : Coefficients.Ring) :
    a • o D (-D.α i) + b • mixedGenerator D i = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hz
    apply (positiveModifiedForm_mixed_coordinates_eq_zero_iff D i a b).mp
    simp only [hz, map_zero, and_self]
  · rintro ⟨rfl, rfl⟩
    simp

/-- Genuine nondegeneracy on the first mixed plane inside the modified quotient. -/
theorem positiveModifiedForm_mixedPlane_nondegenerate (i : I) :
    ((positiveModifiedForm D).restrict (mixedPlane D i)).Nondegenerate := by
  have hu : o D (-D.α i) ∈ mixedPlane D i := Submodule.subset_span (by simp)
  have hm : mixedGenerator D i ∈ mixedPlane D i := Submodule.subset_span (by simp)
  have hp : mixedPivot D i ∈ mixedPlane D i := by
    unfold mixedPivot
    exact (mixedPlane D i).add_mem hm ((mixedPlane D i).smul_mem _ hu)
  have sep : ∀ x : mixedPlane D i, (∀ y : mixedPlane D i,
      positiveModifiedForm D y.val x.val = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp x.property
    have hab := (positiveModifiedForm_mixed_coordinates_eq_zero_iff D i a b).mp
      ⟨he ▸ hx ⟨_, hu⟩, he ▸ hx ⟨_, hp⟩⟩
    apply Subtype.ext
    rw [← he, hab.1, hab.2, zero_smul, zero_smul, add_zero]
    rfl
  constructor
  · intro x hx
    apply sep x
    intro y
    rw [positiveModifiedForm_comm]
    exact hx y
  · exact sep

/-- The mixed generator is an actual triangular tensor, with a unit coefficient. -/
theorem mixedGenerator_eq_triangular (i : I) :
    mixedGenerator D i = qp Coefficients.q (D.d i) •
      triangularModified D Coefficients.q pi (-D.α i)
        (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) ⊗ₜ[Coefficients.Ring]
          D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) := by
  rw [mixedGenerator, rho_e_minus, smul_mul_assoc]
  congr 1
  apply Subtype.ext
  change (f D i 0 : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
    (e D i (-D.α i) : CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      triangularTensor D Coefficients.q pi (-D.α i) _
  simpa [f, e] using (triangularTensor_θ_θ D Coefficients.q pi (-D.α i) i i).symm

private theorem psi_o (μ : X) : psiModified D (o D μ) = o D μ := by
  apply Subtype.ext
  simp [o]

private theorem psi_mixedGenerator (i : I) :
    psiModified D (mixedGenerator D i) =
      (bar (qp Coefficients.q (D.d i)) * D.pii pi i * qp Coefficients.q (-(D.d i : ℤ))) •
        mixedGenerator D i := by
  rw [mixedGenerator, rho_e_minus]
  apply Subtype.ext
  simp only [NonUnitalSubalgebra.coe_smul, NonUnitalSubalgebra.coe_mul, coe_psiModified]
  simp only [e, f, positiveHalf_θ, negativeHalf_θ, psi_smul, map_mul, psi_F, psi_E,
    smul_mul_assoc, smul_smul]
  congr 1
  simp only [RootDatum.parl, map_zero, Int.cast_zero, zero_add, mul_one]
  rw [mul_assoc, qp_mul]
  simp [SuperCartanDatum.pii]

/-- Psi preserves this actual mixed submodule, not just its dimension. -/
theorem psiModified_mem_mixedPlane (i : I) {x : modified D Coefficients.q pi}
    (hx : x ∈ mixedPlane D i) : psiModified D x ∈ mixedPlane D i := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add, map_smulₛₗ, map_smulₛₗ, psi_o, psi_mixedGenerator]
  apply (mixedPlane D i).add_mem
  · exact (mixedPlane D i).smul_mem _ (Submodule.subset_span (by simp))
  · exact (mixedPlane D i).smul_mem _
      ((mixedPlane D i).smul_mem _ (Submodule.subset_span (by simp)))

/-- An explicit detector for the original sesquilinear form and an arbitrary mixed coefficient. -/
theorem sesquilinearForm_mixedPivot_detect (i : I) (a b : Coefficients.Ring) :
    sesquilinearForm D (psiModified D (mixedPivot D i))
      (a • o D (-D.α i) + b • mixedGenerator D i) =
        b * (D.pii pi i * qp Coefficients.q (2 * (D.d i : ℤ)) *
          (D.norm Coefficients.q pi i)^2) := by
  rw [sesquilinearForm_apply, psiModified_psiModified, positiveModifiedForm_mixedPivot_detect]

/-- The original BE2 sesquilinear form is nondegenerate on the mixed plane. -/
theorem sesquilinearForm_mixedPlane_nondegenerate (i : I) :
    LinearMap.Nondegenerate
      ((sesquilinearForm D).domRestrict₁₂ (mixedPlane D i) (mixedPlane D i)) := by
  have hb := positiveModifiedForm_mixedPlane_nondegenerate D i
  constructor
  · intro x hx
    have hz : (⟨psiModified D x.val, psiModified_mem_mixedPlane D i x.property⟩ :
        mixedPlane D i) = 0 :=
      hb.1 _ (fun y ↦ hx y)
    apply Subtype.ext
    have he := congrArg (fun z : mixedPlane D i ↦ psiModified D z.val) hz
    simpa only [psiModified_psiModified, ZeroMemClass.coe_zero, map_zero] using he
  · intro x hx
    apply hb.2
    intro y
    have hh := hx ⟨psiModified D y.val, psiModified_mem_mixedPlane D i y.property⟩
    change positiveModifiedForm D (psiModified D (psiModified D y.val)) x.val = 0 at hh
    change positiveModifiedForm D y.val x.val = 0
    simpa only [psiModified_psiModified] using hh

end OddMath.CoveringQuantum.UDot.GenericTensor

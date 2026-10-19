/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ModifiedFormTransport
import OddMath.CoveringQuantum.UDot.TensorGram.MixedGram

/-!
# Coefficient-bar transports of the native tensor Gram

The two original-algebra input transports and coefficient-barred output give a
bilinear normalized form, preserving rho-adjointness. No module bar or
root-lattice quadratic refinement is assumed. The convention is native cross
Delta1/Delta2 with rho=tau1-prime and source v=q^-1, not an identification with
the printed tau1/Delta3/Delta4 pairing. Clark IV assumes finite, bar-consistent
data; these algebraic transports and adjoint identities do not require those
ambient assumptions. Dominance is retained where the quotient form requires it.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.PolarizationTransport
open Coefficients PreF TensorProduct GenericVerma
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- Two genuine reversals restore multiplication order. -/
def left : CoveringUDot Coefficients.Ring D Coefficients.q pi →+*
    CoveringUDot Coefficients.Ring D Coefficients.q pi where
  toFun u := (rho D Coefficients.q pi pi_sq
    (sigma D Coefficients.q pi pi_sq (psi D Coefficients.q pi bar barData u)).unop).unop
  map_one' := by simp
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

/-- The second input needs a DIFFERENT transport, forced by rho-adjointness. -/
def right : CoveringUDot Coefficients.Ring D Coefficients.q pi →+*
    CoveringUDot Coefficients.Ring D Coefficients.q pi where
  toFun u := (sigma D Coefficients.q pi pi_sq
    (psi D Coefficients.q pi bar barData (rho D Coefficients.q pi pi_sq u).unop)).unop
  map_one' := by simp
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

theorem left_smul (c : Coefficients.Ring) (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    left D (c • u) = bar c • left D u := by simp [left, psi_smul]

theorem right_smul
    (c : Coefficients.Ring) (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    right D (c • u) = bar c • right D u := by simp [right, psi_smul]

@[simp] theorem left_one (μ : X) :
    left D (one D Coefficients.q pi μ) = one D Coefficients.q pi μ := by
  simp [left]
@[simp] theorem right_one (μ : X) :
    right D (one D Coefficients.q pi μ) = one D Coefficients.q pi μ := by
  simp [right]

@[simp] theorem left_E (i : I) (μ : X) :
    left D (E D Coefficients.q pi i μ) =
      qp Coefficients.q (D.d i * (D.h i μ + 1)) • E D Coefficients.q pi i μ := by
  simp only [left, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, psi_E, sigma_E, rho_F,
    add_sub_cancel_right, RootDatum.h, map_add, D.coroot_root, D.isGCM.diag]
  congr 2
  ring

@[simp] theorem left_F (i : I) (μ : X) :
    left D (F D Coefficients.q pi i μ) =
      (pi ^ (D.parl i μ).val * qp Coefficients.q (-(D.d i * (D.h i μ - 1)))) •
        F D Coefficients.q pi i μ := by
  simp only [left, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, psi_F, map_smul,
    MulOpposite.unop_smul, sigma_F, rho_E, sub_add_cancel, smul_smul,
    RootDatum.h, map_sub, D.coroot_root, D.isGCM.diag]
  congr 3
  ring

@[simp] theorem right_E (i : I) (μ : X) :
    right D (E D Coefficients.q pi i μ) =
      (pi ^ (D.parl i μ).val * qp Coefficients.q (D.d i * (D.h i μ + 1))) •
        E D Coefficients.q pi i μ := by
  simp [right, psi_smul, barData.map_qp, D.parl_add_α, smul_smul, mul_comm]

@[simp] theorem right_F (i : I) (μ : X) :
    right D (F D Coefficients.q pi i μ) =
      qp Coefficients.q (-(D.d i * (D.h i μ - 1))) • F D Coefficients.q pi i μ := by
  simp [right, psi_smul, barData.map_qp]

/-- Exact opposite/reversal identity on all original elements. -/
theorem right_rho (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    right D (rho D Coefficients.q pi pi_sq u).unop =
      (rho D Coefficients.q pi pi_sq (left D u)).unop := by
  simp only [right, left, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, rho_rho]

/-- Concrete semilinear restrictions, with actual modified-subalgebra membership. -/
def leftModified : modified D Coefficients.q pi →ₛₗ[bar] modified D Coefficients.q pi :=
  (rhoModified D Coefficients.q pi pi_sq).comp
    ((sigmaModified D Coefficients.q pi pi_sq).comp (GenericTensor.psiModified D))

def rightModified : modified D Coefficients.q pi →ₛₗ[bar] modified D Coefficients.q pi :=
  (sigmaModified D Coefficients.q pi pi_sq).comp
    ((GenericTensor.psiModified D).comp (rhoModified D Coefficients.q pi pi_sq))

@[simp] theorem coe_leftModified (u : modified D Coefficients.q pi) :
    (leftModified D u : CoveringUDot Coefficients.Ring D Coefficients.q pi) = left D u := rfl
@[simp] theorem coe_rightModified (u : modified D Coefficients.q pi) :
    (rightModified D u : CoveringUDot Coefficients.Ring D Coefficients.q pi) = right D u := rfl

theorem leftModified_mul (u v : modified D Coefficients.q pi) :
    leftModified D (u * v) = leftModified D u * leftModified D v :=
  Subtype.ext (map_mul (left D) u.val v.val)
theorem rightModified_mul (u v : modified D Coefficients.q pi) :
    rightModified D (u * v) = rightModified D u * rightModified D v :=
  Subtype.ext (map_mul (right D) u.val v.val)

variable (Λ Μ : X)

/-- Actual action, with the scalar twist EXPLICIT in its codomain. -/
def action (side s : Bool) :
    CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    Twist bar (Module.End Coefficients.Ring
      (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ)) where
  __ := (Twist.of bar).toRingHom.comp
    ((tensorRepresentation D Λ Μ s).toRingHom.comp (if side then left D else right D))
  commutes' c := by
    change tensorRepresentation D Λ Μ s
      ((if side then left D else right D) (algebraMap Coefficients.Ring _ c)) =
        algebraMap Coefficients.Ring _ (bar c)
    rw [Algebra.algebraMap_eq_smul_one]
    cases side <;> simp [left_smul, right_smul, Algebra.algebraMap_eq_smul_one]

/-- This includes EVERY original relation (mixed and both connected Serre families). -/
theorem action_rel (side s : Bool) {u v : Free Coefficients.Ring I X}
    (h : Rel D Coefficients.q pi u v) :
    action D Λ Μ side s (mk D Coefficients.q pi u) =
      action D Λ Μ side s (mk D Coefficients.q pi v) := by
  exact congrArg (action D Λ Μ side s) (RingQuot.mkAlgHom_rel Coefficients.Ring h)

abbrev vac := toIntegrable D Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D Μ 1

/-- Bilinear, not sesquilinear: both inputs and the OUTPUT are coefficient-barred. -/
def gram (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) :
    LinearMap.BilinForm Coefficients.Ring (CoveringUDot Coefficients.Ring D Coefficients.q pi) where
  toFun u :=
    { toFun := fun v ↦ bar (tensorPolarization D Λ Μ hΛ hΜ
        (tensorRepresentation D Λ Μ s (left D u) (vac D Λ Μ))
        (tensorRepresentation D Λ Μ (!s) (right D v) (vac D Λ Μ)))
      map_add' := by intro v w; simp
      map_smul' := by intro c v; simp [right_smul, bar_bar] }
  map_add' := by intro u v; ext w; simp
  map_smul' := by intro c u; ext v; simp [left_smul, bar_bar]

@[simp] theorem gram_apply (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    gram D Λ Μ hΛ hΜ s u v = bar (tensorPolarization D Λ Μ hΛ hΜ
      (tensorRepresentation D Λ Μ s (left D u) (vac D Λ Μ))
      (tensorRepresentation D Λ Μ (!s) (right D v) (vac D Λ Μ))) := rfl

/-- Original rho, with its scalar contractions, survives the input transport. -/
theorem gram_adjoint (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u x y : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    gram D Λ Μ hΛ hΜ s (u*x) y =
      gram D Λ Μ hΛ hΜ s x ((rho D Coefficients.q pi pi_sq u).unop*y) := by
  simp only [gram_apply, map_mul, Module.End.mul_apply, right_rho]
  rw [tensorPolarization_adjoint]

/-- Restriction to the genuine nonunital modified algebra. -/
def modifiedGram (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) :
    LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi) :=
  (gram D Λ Μ hΛ hΜ s).compl₁₂
    (modified D Coefficients.q pi).subtype (modified D Coefficients.q pi).subtype

end OddMath.CoveringQuantum.UDot.PolarizationTransport

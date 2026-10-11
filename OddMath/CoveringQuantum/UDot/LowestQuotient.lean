import OddMath.CoveringQuantum.UDot.IntegrablePolarization

/-!
# The actual Clark lowest-weight quotient

Clark, arXiv:1312.4855v2, §2.3 defines a **linear**, generally non-involutive
omega. It is not BE2's scalar-bar-semilinear omega. Composing the existing
BE2 omega and psi gives Clark's algebra equivalence on the actual presentation,
with E mapped to F and F mapped to pi^(parity*(h+1)) E at the negated weight.
Pullback gives a genuine lowest action on the accepted source-generated
integrability quotient, not a newly postulated module.

The unchanged original form is a cross-polarization between omega and its
inverse: `rho_clarkOmega` and `lowest_cross_adjoint` retain that inverse.
They hold on arbitrary quotient vectors. They do not identify the two twists.

This is a prerequisite for the mixed tensor comparison in Clark §5.3,
Propositions 5.10–5.11, not their proof. In the present v=q^-1 convention the
accepted form uses tau1-prime (Clark Proposition 5.8), whereas §5.3's printed
Delta3/Delta4 pairing uses tau1. Coproduct/form transport is still required.
No tensor action, local nilpotence, irreducibility or nondegeneracy is asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- Clark's linear omega, distinct from BE2's antilinear omega. -/
def clarkOmega : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    CoveringUDot Coefficients.Ring D Coefficients.q pi where
  __ := (omega D Coefficients.q pi bar barData).comp (psi D Coefficients.q pi bar barData)
  commutes' c := by
    change omega D Coefficients.q pi bar barData
      (psi D Coefficients.q pi bar barData (algebraMap Coefficients.Ring _ c)) = _
    rw [psi_algebraMap, omega_algebraMap, bar_bar]

/-- The inverse of Clark's linear omega. -/
def clarkOmegaInv : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    CoveringUDot Coefficients.Ring D Coefficients.q pi where
  __ := (psi D Coefficients.q pi bar barData).comp (omega D Coefficients.q pi bar barData)
  commutes' c := by
    change psi D Coefficients.q pi bar barData
      (omega D Coefficients.q pi bar barData (algebraMap Coefficients.Ring _ c)) = _
    rw [omega_algebraMap, psi_algebraMap, bar_bar]

@[simp] theorem clarkOmega_one (μ : X) :
    clarkOmega D (one D Coefficients.q pi μ) = one D Coefficients.q pi (-μ) := by
  simp [clarkOmega]

@[simp] theorem clarkOmega_E (i : I) (μ : X) :
    clarkOmega D (E D Coefficients.q pi i μ) = F D Coefficients.q pi i (-μ) := by
  simp [clarkOmega]

@[simp] theorem clarkOmega_F (i : I) (μ : X) :
    clarkOmega D (F D Coefficients.q pi i μ) =
      pi ^ (D.parl i μ).val • E D Coefficients.q pi i (-μ) := by
  simp [clarkOmega, omega_smul, bar_pi]

@[simp] theorem clarkOmegaInv_one (μ : X) :
    clarkOmegaInv D (one D Coefficients.q pi μ) = one D Coefficients.q pi (-μ) := by
  simp [clarkOmegaInv]

@[simp] theorem clarkOmegaInv_E (i : I) (μ : X) :
    clarkOmegaInv D (E D Coefficients.q pi i μ) =
      pi ^ (D.parl i (-μ)).val • F D Coefficients.q pi i (-μ) := by
  simp [clarkOmegaInv]

@[simp] theorem clarkOmegaInv_F (i : I) (μ : X) :
    clarkOmegaInv D (F D Coefficients.q pi i μ) = E D Coefficients.q pi i (-μ) := by
  simp [clarkOmegaInv]

@[simp] theorem clarkOmegaInv_clarkOmega
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    clarkOmegaInv D (clarkOmega D u) = u := by
  change psi D Coefficients.q pi bar barData
    (omega D Coefficients.q pi bar barData
      (omega D Coefficients.q pi bar barData (psi D Coefficients.q pi bar barData u))) = u
  rw [omega_omega barData bar_bar, psi_psi barData bar_bar]

@[simp] theorem clarkOmega_clarkOmegaInv
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    clarkOmega D (clarkOmegaInv D u) = u := by
  change omega D Coefficients.q pi bar barData
    (psi D Coefficients.q pi bar barData
      (psi D Coefficients.q pi bar barData (omega D Coefficients.q pi bar barData u))) = u
  rw [psi_psi barData bar_bar, omega_omega barData bar_bar]

/-- Clark omega is an actual algebra equivalence of the existing presentation. -/
def clarkOmegaEquiv : CoveringUDot Coefficients.Ring D Coefficients.q pi ≃ₐ[Coefficients.Ring]
    CoveringUDot Coefficients.Ring D Coefficients.q pi :=
  AlgEquiv.ofAlgHom (clarkOmega D) (clarkOmegaInv D)
    (AlgHom.ext (clarkOmega_clarkOmegaInv D))
    (AlgHom.ext (clarkOmegaInv_clarkOmega D))

omit [DecidableEq I] [DecidableEq X] in
private theorem parl_neg (i : I) (μ : X) : D.parl i (-μ) = D.parl i μ := by
  simp only [RootDatum.parl, RootDatum.h, map_neg, Int.cast_neg]
  have hn : ∀ z : ZMod 2, -z = z := by decide
  rw [hn]

/-- Rho intertwines the two inverse Clark twists, rather than commuting with omega. -/
theorem rho_clarkOmega (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    (rho D Coefficients.q pi pi_sq (clarkOmega D u)).unop =
      clarkOmegaInv D (rho D Coefficients.q pi pi_sq u).unop := by
  obtain ⟨u, rfl⟩ := mk_surjective D Coefficients.q pi u
  induction u using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 g =>
    cases g with
    | one μ =>
      change (rho D Coefficients.q pi pi_sq (clarkOmega D (one D Coefficients.q pi μ))).unop =
        clarkOmegaInv D (rho D Coefficients.q pi pi_sq (one D Coefficients.q pi μ)).unop
      simp
    | e i μ =>
      change (rho D Coefficients.q pi pi_sq (clarkOmega D (E D Coefficients.q pi i μ))).unop =
        clarkOmegaInv D (rho D Coefficients.q pi pi_sq (E D Coefficients.q pi i μ)).unop
      simp only [clarkOmega_E, rho_F, rho_E, map_smul, clarkOmegaInv_F,
        RootDatum.h, map_neg]
      congr 2
      · ring
      · abel
    | f i μ =>
      change (rho D Coefficients.q pi pi_sq (clarkOmega D (F D Coefficients.q pi i μ))).unop =
        clarkOmegaInv D (rho D Coefficients.q pi pi_sq (F D Coefficients.q pi i μ)).unop
      simp only [clarkOmega_F, map_smul, MulOpposite.unop_smul, rho_E, rho_F,
        clarkOmegaInv_E, parl_neg, D.parl_sub_α, RootDatum.h, map_neg, smul_smul]
      have h : -(D.d i * (-(D.cd.coroot i) μ + 1)) =
          D.d i * ((D.cd.coroot i) μ - 1) := by ring
      rw [h, mul_comm]
      congr 2
      abel
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, MulOpposite.unop_mul, ha, hb]

namespace GenericVerma
variable [Finite I] (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

/-- The genuine omega-twisted source quotient, with the original quotient carrier. -/
def lowestRepresentation : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (integrableRepresentation D hD Λ).comp (clarkOmega D)

/-- The inverse-twisted source quotient, needed for the cross-polarization. -/
def lowestInverseRepresentation : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (integrableRepresentation D hD Λ).comp (clarkOmegaInv D)

@[simp] theorem lowestRepresentation_one (μ : X) :
    lowestRepresentation D hD Λ (one D Coefficients.q pi μ) =
      integrableRepresentation D hD Λ (one D Coefficients.q pi (-μ)) := by
  simp [lowestRepresentation]

@[simp] theorem lowestRepresentation_E (i : I) (μ : X) :
    lowestRepresentation D hD Λ (E D Coefficients.q pi i μ) =
      integrableRepresentation D hD Λ (F D Coefficients.q pi i (-μ)) := by
  simp [lowestRepresentation]

@[simp] theorem lowestRepresentation_F (i : I) (μ : X) :
    lowestRepresentation D hD Λ (F D Coefficients.q pi i μ) =
      pi ^ (D.parl i μ).val • integrableRepresentation D hD Λ (E D Coefficients.q pi i (-μ)) := by
  simp [lowestRepresentation]

/-- Arbitrary representatives compute through the original action, not a substituted module. -/
@[simp] theorem lowestRepresentation_toIntegrable
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) (x : D.serreF Coefficients.q pi) :
    lowestRepresentation D hD Λ u (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (representation D hD Λ (clarkOmega D u) x) := rfl

/-- The transported vacuum has weight minus Lambda. -/
@[simp] theorem lowestRepresentation_vacuum_weight (μ : X) :
    lowestRepresentation D hD Λ (one D Coefficients.q pi μ) (toIntegrable D hD Λ 1) =
      if μ = -Λ then toIntegrable D hD Λ 1 else 0 := by
  rw [lowestRepresentation_toIntegrable, clarkOmega_one, representation_one, weightProject_one]
  have he : -μ = Λ ↔ μ = -Λ := neg_eq_iff_eq_neg
  simp only [he]
  split_ifs <;> simp

/-- Every negative Chevalley generator kills the actual lowest vector. -/
@[simp] theorem lowestRepresentation_F_vacuum (i : I) (μ : X) :
    lowestRepresentation D hD Λ (F D Coefficients.q pi i μ) (toIntegrable D hD Λ 1) = 0 := by
  rw [lowestRepresentation_F, LinearMap.smul_apply, integrableRepresentation_E_mk,
    weightProject_one]
  split_ifs <;> simp

/-- The unchanged original form pairs the omega and inverse-omega actions.
This is not same-action polarization: the inverse twist is essential at pi=-1. -/
theorem lowest_cross_adjoint (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (lowestRepresentation D hD Λ u x) y =
      integrablePolarization D hD Λ hΛ x
        (lowestInverseRepresentation D hD Λ (rho D Coefficients.q pi pi_sq u).unop y) := by
  change integrablePolarization D hD Λ hΛ (integrableRepresentation D hD Λ (clarkOmega D u) x) y = _
  rw [integrablePolarization_adjoint, rho_clarkOmega]
  rfl

end GenericVerma
end OddMath.CoveringQuantum.UDot

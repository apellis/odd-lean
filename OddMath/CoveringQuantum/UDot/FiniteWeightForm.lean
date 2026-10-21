/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.FiniteWeightAlgebra
import OddMath.CoveringQuantum.UDot.SesquilinearForm

/-!
# Evaluation transport of the modified sesquilinear form

The finite-free-lattice form comparison used in the finite-support route to
Brundan–Ellis, arXiv:1701.04133v2, Theorem 12.1. The existing forms of §10
are compared using their uniqueness characterization and the original §9
symmetries. Integral biduality retains the full lattice, including central
weights, as in the perfect-pairing setup of Clark, arXiv:1312.4855v2, §2.1.
This comparison needs neither bar consistency nor independence of roots,
and is not categorical nondegeneracy or finite-support descent.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot.FiniteWeightForm

open FiniteWeightDuality FiniteWeightAlgebra GenericTensor Coefficients PreF

variable {k I L : Type*} [CommRing k] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)]
variable (D : RootDatum I L) (q : kˣ) (π : k)

/-- Evaluation commutes with the original linear antiautomorphism. -/
theorem forward_rho (hπ : π ^ 2 = 1) (x : CoveringUDot k D q π) :
    forward D q π (rho D q π hπ x).unop =
      (rho (dualDatum D) q π hπ (forward D q π x)).unop := by
  obtain ⟨x, rfl⟩ := mk_surjective D q π x
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  | grade1 g =>
    cases g with
    | one μ =>
      rw [← Free.one, ← one]
      simp only [rho_one, forward_one]
    | e i μ =>
      rw [← Free.E, ← E]
      simp only [rho_E, map_smul, forward_E, forward_F, map_add,
        weightEquiv_root, coroot_weightEquiv]
    | f i μ =>
      rw [← Free.F, ← F]
      simp only [rho_F, map_smul, forward_E, forward_F, map_sub,
        weightEquiv_root, coroot_weightEquiv]
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, MulOpposite.unop_mul, ha, hb]

/-- Evaluation commutes with the original scalar-bar automorphism. -/
theorem forward_psi (σ : k →+* k) (hσ : BarData q π σ) (x : CoveringUDot k D q π) :
    forward D q π (psi D q π σ hσ x) =
      psi (dualDatum D) q π σ hσ (forward D q π x) := by
  obtain ⟨x, rfl⟩ := mk_surjective D q π x
  induction x using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes, psi_algebraMap]
  | grade1 g =>
    cases g with
    | one μ =>
      rw [← Free.one, ← one]
      simp only [psi_one, forward_one]
    | e i μ =>
      rw [← Free.E, ← E]
      simp only [psi_E, forward_E]
    | f i μ =>
      rw [← Free.F, ← F]
      simp only [psi_F, map_smul, forward_F, RootDatum.parl,
        coroot_weightEquiv]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

/-- The fixed nonunital equivalence intertwines rho. -/
theorem modifiedEquiv_rho (hπ : π ^ 2 = 1) (x : modified D q π) :
    modifiedEquiv D q π (rhoModified D q π hπ x) =
      rhoModified (dualDatum D) q π hπ (modifiedEquiv D q π x) :=
  Subtype.ext (forward_rho D q π hπ x.val)

omit [DecidableEq I] [DecidableEq L] [DecidableEq (coweight L →+ ℤ)] in
/-- Signed root weights are evaluated without changing their half-algebra degree. -/
theorem weightEquiv_halfWeight (positive : Bool) (ν : I →₀ ℕ) :
    weightEquiv L (halfWeight D positive ν) = halfWeight (dualDatum D) positive ν := by
  cases positive <;> simp [halfWeight, halfRoot, Finsupp.sum, map_sum, weightEquiv_root]

/-- Evaluation sends each signed word to the same word with evaluated endpoints. -/
theorem forward_halfWord (positive : Bool) (w : List I) (μ : L) :
    forward D q π (halfWord D q π positive w μ) =
      halfWord (dualDatum D) q π positive w (weightEquiv L μ) := by
  induction w with
  | nil => exact forward_one D q π μ
  | cons i w ih =>
    cases positive <;>
      simp only [halfWord, halfGen, Bool.false_eq_true, ↓reduceIte, map_mul,
        forward_E, forward_F, map_add, weightEquiv_halfWeight, ih]

/-- The same Serre half algebra maps to the evaluated positive half. -/
theorem modifiedEquiv_positiveHalf (μ : L) (x : D.serreF q π) :
    modifiedEquiv D q π (positiveHalf D q π μ x) =
      positiveHalf (dualDatum D) q π (weightEquiv L μ) x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective q π x
  induction x using induction_monomial with
  | word w =>
    apply Subtype.ext
    change forward D q π (halfMap D q π true μ _) = halfMap (dualDatum D) q π true _ _
    rw [halfMap_monomial, halfMap_monomial, forward_halfWord]
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]


/-- The fixed nonunital equivalence intertwines psi over the generic ring. -/
theorem modifiedEquiv_psi (x : modified D Coefficients.q pi) :
    modifiedEquiv D Coefficients.q pi (psiModified D x) =
      psiModified (dualDatum D) (modifiedEquiv D Coefficients.q pi x) :=
  Subtype.ext (forward_psi D Coefficients.q pi bar barData x.val)

/-- The original star, rather than an adjoint chosen from the form, is transported. -/
theorem modifiedEquiv_star (x : modified D Coefficients.q pi) :
    modifiedEquiv D Coefficients.q pi (starModified D x) =
      starModified (dualDatum D) (modifiedEquiv D Coefficients.q pi x) := by
  change modifiedEquiv D Coefficients.q pi (rhoModified D Coefficients.q pi pi_sq
    (psiModified D x)) = rhoModified (dualDatum D) Coefficients.q pi pi_sq
      (psiModified (dualDatum D) (modifiedEquiv D Coefficients.q pi x))
  rw [modifiedEquiv_rho, modifiedEquiv_psi]

/-- Evaluation preserves the existing positive-normalized bilinear form. -/
theorem positiveModifiedForm_modifiedEquiv (x y : modified D Coefficients.q pi) :
    positiveModifiedForm (dualDatum D) (modifiedEquiv D Coefficients.q pi x)
      (modifiedEquiv D Coefficients.q pi y) = positiveModifiedForm D x y := by
  let e := modifiedEquiv D Coefficients.q pi
  let B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi) :=
    (positiveModifiedForm (dualDatum D)).compl₁₂ e.toLinearMap e.toLinearMap
  have he : B = positiveModifiedForm D := by
    apply positiveModifiedForm_unique D B
    · intro μ ν μ' ν' a b ha hb hn
      apply positiveModifiedForm_orthogonal (dualDatum D)
        (weightEquiv L μ) (weightEquiv L ν) (weightEquiv L μ') (weightEquiv L ν')
        (e a) (e b) (forward_mem_block D Coefficients.q pi ha)
        (forward_mem_block D Coefficients.q pi hb)
      exact hn.imp (fun h he ↦ h ((weightEquiv L).injective he))
        (fun h he ↦ h ((weightEquiv L).injective he))
    · intro u a b
      change positiveModifiedForm (dualDatum D) (e (u * a)) (e b) =
        positiveModifiedForm (dualDatum D) (e a)
          (e (rhoModified D Coefficients.q pi pi_sq u * b))
      simp only [e, modifiedEquiv_mul, positiveModifiedForm_adjoint, modifiedEquiv_rho]
    · intro μ a b
      change positiveModifiedForm (dualDatum D)
        (modifiedEquiv D Coefficients.q pi (positiveHalf D Coefficients.q pi μ a))
        (modifiedEquiv D Coefficients.q pi (positiveHalf D Coefficients.q pi μ b)) = _
      rw [modifiedEquiv_positiveHalf, modifiedEquiv_positiveHalf,
        positiveModifiedForm_positiveHalf]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- The existing generic sesquilinear forms agree under the fixed nonunital
modified-algebra equivalence. No form-compatibility premise, root independence,
finite-colour assumption, or bar-consistency assumption is required. -/
theorem sesquilinearForm_modifiedEquiv (x y : modified D Coefficients.q pi) :
    sesquilinearForm (dualDatum D) (modifiedEquiv D Coefficients.q pi x)
      (modifiedEquiv D Coefficients.q pi y) = sesquilinearForm D x y := by
  rw [sesquilinearForm_apply, ← modifiedEquiv_psi, positiveModifiedForm_modifiedEquiv,
    sesquilinearForm_apply]

omit [DecidableEq (coweight L →+ ℤ)] in
/-- Finite-colour, finite-free-lattice left-radical theorem on the original
weight lattice. Root and coroot independence and bar consistency are retained;
this intermediate does not assert nondegeneracy for arbitrary ambient lattices. -/
theorem sesquilinearForm_nondegenerate [Finite I]
    (hD : D.toSuperCartanDatum.BarConsistent)
    (hα : LinearIndependent ℤ D.α) (hh : LinearIndependent ℤ D.cd.coroot)
    (x : modified D Coefficients.q pi)
    (hx : ∀ y, sesquilinearForm D x y = 0) : x = 0 := by
  classical
  have he : modifiedEquiv D Coefficients.q pi x = 0 := by
    apply UDot.sesquilinearForm_nondegenerate (realization D) hD
      (root_independent D hα) (coroot_independent D hh)
    intro y
    obtain ⟨y, rfl⟩ := (modifiedEquiv D Coefficients.q pi).surjective y
    rw [sesquilinearForm_modifiedEquiv]
    exact hx y
  exact (modifiedEquiv D Coefficients.q pi).injective
    (he.trans (map_zero (modifiedEquiv D Coefficients.q pi)).symm)

end OddMath.CoveringQuantum.UDot.FiniteWeightForm

namespace OddMath.CoveringQuantum.UDot.FiniteWeightForm

open Coefficients GenericTensor SourceWeightLattice

open scoped Classical in
/-- The finite-stage radical theorem on source complex windows. The ambient
colour set and complex space need not be finite. This concerns each window's
own algebra, not descent of an ambient radical element into such a window. -/
theorem sourceWindow_nondegenerate {I H : Type*} [AddCommGroup H] [Module ℂ H]
    (h : I → H) (C : SuperCartanDatum I) (α : I → Module.Dual ℂ H)
    (ha : ∀ i j, α j (h i) = (C.a i j : ℂ))
    (hh : LinearIndependent ℂ h) (hα : LinearIndependent ℂ α)
    (hC : C.BarConsistent) (J : Finset I) (W : Finset (weightLattice h))
    (x : modified (windowDatum h C α ha hh J W) Coefficients.q pi)
    (hx : ∀ y, sesquilinearForm (windowDatum h C α ha hh J W) x y = 0) : x = 0 := by
  apply sesquilinearForm_nondegenerate (windowDatum h C α ha hh J W)
    (fun i ↦ hC i) (window_root_linearIndependent h C α ha hh J W hα)
    (window_coroot_linearIndependent h C α ha hh J W) x hx

end OddMath.CoveringQuantum.UDot.FiniteWeightForm

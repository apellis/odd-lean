/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ColumnFunctional

/-!
# Transport-compatible column contraction

This auxiliary construction accepts a linear involution of the actual modified
algebra and a half-algebra bilinear form. Its normalization theorem requires
only the involution's proved word formula and half-form orthogonality, not any
existence or laws of a full modified-algebra form. These hypotheses are discharged
for concrete maps in `NegativeColumnFunctional`.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)
variable (A : modified D Coefficients.q pi →ₗ[Coefficients.Ring] modified D Coefficients.q pi)
variable (H : LinearMap.BilinForm Coefficients.Ring (D.serreF Coefficients.q pi))

/-- Correct triangular coordinates by a specified actual linear adjoint map. -/
def adjointUndo (μ : X) :
    D.serreF Coefficients.q pi →ₗ[Coefficients.Ring] D.serreF Coefficients.q pi :=
  (positiveTotal D).comp (A.comp (negativeRow D μ))

/-- A functional built from half data and the actual triangular retraction. -/
def adjointColumn (μ : X) : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₗ[Coefficients.Ring]
    Coefficients.Ring :=
  (TensorProduct.lift (LinearMap.comp H (adjointUndo D A μ))).comp (tensorEval D μ)

@[simp] theorem adjointColumn_triangularTensor (μ : X) (x y : D.serreF Coefficients.q pi) :
    adjointColumn D A H μ (triangularTensor D Coefficients.q pi μ (x ⊗ₜ[Coefficients.Ring] y)) =
      H (adjointUndo D A μ x) y := by
  simp [adjointColumn]

variable (hA : ∀ x, A (A x) = x)
variable (hAw : ∀ μ w, ∃ c : Coefficients.Ringˣ,
  (A (positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) :
    CoveringUDot Coefficients.Ring D Coefficients.q pi) =
  (c : Coefficients.Ring) • halfWord D Coefficients.q pi false w.reverse
    (μ + halfWeight D true (wordWeight w)))
variable (hH : ∀ a b, halfWeight D true (wordWeight a) ≠ halfWeight D true (wordWeight b) →
  H (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
    (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) = 0)

include hA in
theorem adjointUndo_word (μ : X) (w : List I) (c : Coefficients.Ringˣ)
    (hc : (A (positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) :
        CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      (c : Coefficients.Ring) • halfWord D Coefficients.q pi false w.reverse
        (μ + halfWeight D true (wordWeight w))) :
    adjointUndo D A μ ((c : Coefficients.Ring) •
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w.reverse)) =
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  have hw : wordWeight w.reverse = wordWeight w := by simp [wordWeight, List.map_reverse]
  have hr : negativeRow D μ ((c : Coefficients.Ring) •
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w.reverse)) =
      A (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) := by
    rw [map_smul, negativeRow_monomial, hw]
    apply Subtype.ext
    change (c : Coefficients.Ring) • halfMap D Coefficients.q pi false _ _ = _
    rw [halfMap_monomial]
    exact hc.symm
  change positiveTotal D (A (negativeRow D μ _)) = _
  rw [hr, hA, positiveTotal_half]

include hA hAw hH in
/-- Half-pair normalization follows from verified adjoint word identities and
half-form orthogonality; no full-form laws are premises. -/
theorem adjointColumn_halfWord (μ : X) (a b : List I) :
    adjointColumn D A H μ
      ((A (positiveHalf D Coefficients.q pi μ
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))) :
          CoveringUDot Coefficients.Ring D Coefficients.q pi) *
        halfWord D Coefficients.q pi true b μ) =
      H (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) := by
  obtain ⟨c, hc⟩ := hAw μ a
  by_cases hw : halfWeight D true (wordWeight a) = halfWeight D true (wordWeight b)
  · rw [hc, smul_mul_assoc]
    have hn : halfWord D Coefficients.q pi false a.reverse (μ + halfWeight D true (wordWeight a)) *
        halfWord D Coefficients.q pi true b μ = normalWord D Coefficients.q pi a.reverse b μ := by
      rw [hw]; rfl
    rw [hn, ← triangularTensor_monomial, ← map_smul, TensorProduct.smul_tmul',
      adjointColumn_triangularTensor, adjointUndo_word D A hA μ a c hc]
  · rw [hc]
    have ha := halfWord_mem_block D Coefficients.q pi false a.reverse
      (μ + halfWeight D true (wordWeight a))
    have hb := halfWord_mem_block D Coefficients.q pi true b μ
    rw [smul_mul_assoc, mul_eq_zero_of_mem_block D Coefficients.q pi ha hb
      (fun h ↦ hw (add_left_cancel h)), smul_zero, map_zero, hH a b hw]

include hA hAw hH in
/-- The normalization includes arbitrary nonhomogeneous half-algebra pairs. -/
theorem adjointColumn_halfMap (μ : X) (x y : D.serreF Coefficients.q pi) :
    adjointColumn D A H μ
      ((A (positiveHalf D Coefficients.q pi μ x) :
          CoveringUDot Coefficients.Ring D Coefficients.q pi) *
        halfMap D Coefficients.q pi true μ y) = H x y := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction x using induction_monomial with
  | zero => simp
  | add x z hx hz =>
    simp only [map_add, NonUnitalSubalgebra.coe_add, add_mul, hx, hz, LinearMap.add_apply]
  | smul c x hx =>
    simp only [map_smul, NonUnitalSubalgebra.coe_smul, smul_mul_assoc, hx, LinearMap.smul_apply]
  | word a =>
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simp only [map_add, mul_add, hy, hz]
    | smul c y hy => simp only [map_smul, mul_smul_comm, hy]
    | word b => rw [halfMap_monomial]; exact adjointColumn_halfWord D A H hA hAw hH μ a b

end OddMath.CoveringQuantum.UDot.GenericTensor

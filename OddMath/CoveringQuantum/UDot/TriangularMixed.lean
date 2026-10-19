/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TriangularWeights
import OddMath.CoveringQuantum.UDot.VermaMixed

/-!
# The weight-projected regular mixed relation

The toral eigenvalues are computed on monomial tensors. Projection groups actual
weights, and the unit covering denominator converts the correction to the exact
quantum integer in the modified presentation.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
private theorem weight_monomial (v : Coefficients.Ringˣ) (i : I) (w : List I) :
    weight D.toSuperCartanDatum v i (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
      ((D.qi v i ^ D.h i (halfWeight D true (wordWeight w)) : Coefficients.Ringˣ) :
    Coefficients.Ring) •
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  rw [weight, diagonal_mk]
  change D.toSerreF Coefficients.q pi (weightTwist D.toSuperCartanDatum v i _) = _
  rw [weightTwist_monomial, map_smul]

omit [DecidableEq I] [DecidableEq X] in
/-- The toral operator has the expected eigenvalue on a homogeneous tensor. -/
theorem toral_monomial (v : Coefficients.Ringˣ) (i : I) (a b : List I) :
    toral D.toSuperCartanDatum v i
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) =
      ((D.qi v i ^ (D.h i (halfWeight D true (wordWeight b)) -
        D.h i (halfWeight D true (wordWeight a))) : Coefficients.Ringˣ) : Coefficients.Ring) •
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) := by
  simp only [toral, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, weight_monomial,
    smul_tmul, tmul_smul, smul_smul]
  congr 1
  have hinv : D.qi v⁻¹ i = (D.qi v i)⁻¹ := by simp [SuperCartanDatum.qi]
  rw [hinv, inv_zpow, ← zpow_neg, ← Units.val_mul, ← zpow_add]
  simp only [sub_eq_add_neg]

private def correction (μ : X) (i : I) : Module.End Coefficients.Ring
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  Ring.inverse (vermaDenominator D.toSuperCartanDatum Coefficients.q pi i) •
    (((D.qi Coefficients.q i ^ D.h i μ : Coefficients.Ringˣ) : Coefficients.Ring) •
      toral D.toSuperCartanDatum Coefficients.q i +
    (-(D.pii pi i ^ (D.h i μ).natAbs *
      ((D.qi Coefficients.q i ^ (-D.h i μ) : Coefficients.Ringˣ) : Coefficients.Ring))) •
      toral D.toSuperCartanDatum Coefficients.q⁻¹ i)

omit [DecidableEq I] [DecidableEq X] in
private theorem correction_monomial (μ : X) (i : I) (a b : List I) :
    correction D μ i
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) =
      qpInt (D.qi Coefficients.q i) (D.pii pi i)
        (D.h i (μ - halfWeight D true (wordWeight a) + halfWeight D true (wordWeight b))) •
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) := by
  simp only [correction, LinearMap.smul_apply, LinearMap.add_apply, toral_monomial,
    smul_smul, ← add_smul]
  congr 1
  have hp : D.pii pi i ^ (D.h i (μ - halfWeight D true (wordWeight a) +
      halfWeight D true (wordWeight b))).natAbs = D.pii pi i ^ (D.h i μ).natAbs := by
    simp only [map_add, map_sub]
    rw [show D.h i μ - D.h i (halfWeight D true (wordWeight a)) +
        D.h i (halfWeight D true (wordWeight b)) =
      (D.h i μ + D.h i (halfWeight D true (wordWeight b))) -
        D.h i (halfWeight D true (wordWeight a)) by omega,
      pii_pow_sub_word D pi pi_sq]
    have h := pii_pow_sub_word D pi pi_sq i
      (D.h i μ + D.h i (halfWeight D true (wordWeight b))) b
    simpa only [add_sub_cancel_right] using h.symm
  have hinv : D.qi Coefficients.q⁻¹ i = (D.qi Coefficients.q i)⁻¹ := by simp [SuperCartanDatum.qi]
  have he :
      ((D.qi Coefficients.q i ^ D.h i μ : Coefficients.Ringˣ) : Coefficients.Ring) *
        ((D.qi Coefficients.q i ^ (D.h i (halfWeight D true (wordWeight b)) -
          D.h i (halfWeight D true (wordWeight a))) : Coefficients.Ringˣ) : Coefficients.Ring) +
      (-(D.pii pi i ^ (D.h i μ).natAbs *
        ((D.qi Coefficients.q i ^ (-D.h i μ) : Coefficients.Ringˣ) : Coefficients.Ring))) *
        ((D.qi Coefficients.q⁻¹ i ^ (D.h i (halfWeight D true (wordWeight b)) -
          D.h i (halfWeight D true (wordWeight a))) : Coefficients.Ringˣ) : Coefficients.Ring) =
      vermaDenominator D.toSuperCartanDatum Coefficients.q pi i *
        qpInt (D.qi Coefficients.q i) (D.pii pi i)
          (D.h i (μ - halfWeight D true (wordWeight a) + halfWeight D true (wordWeight b))) := by
    rw [denominator_qpInt D Coefficients.q pi pi_sq, hp, hinv]
    simp only [RootDatum.h, map_add, map_neg, inv_zpow, ← zpow_neg, neg_mul, mul_assoc,
      ← Units.val_mul, ← zpow_add, sub_eq_add_neg, neg_add_rev, neg_neg]
    simp only [add_comm, add_left_comm, add_assoc]
  rw [he, ← mul_assoc, Ring.inverse_mul_cancel _ (GenericVerma.vermaDenominator_isUnit
    D.toSuperCartanDatum i), one_mul]

omit [DecidableEq I] [DecidableEq X] in
private theorem correction_project (μ ν : X) (i : I) :
    correction D μ i * weightProject D μ ν =
      qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i ν) • weightProject D μ ν := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply,
    ]
  change correction D μ i (weightProject D μ ν _) =
    qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i ν) • weightProject D μ ν _
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction x using induction_monomial with
  | zero => simp
  | add x z hx hz => simp only [map_add, add_tmul, hx, hz, smul_add]
  | smul c x hx => simp only [map_smul, smul_tmul, tmul_smul, hx, smul_comm c]
  | word a =>
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simp only [map_add, tmul_add, hy, hz, smul_add]
    | smul c y hy => simp only [map_smul, tmul_smul, hy, smul_comm c]
    | word b =>
      rw [weightProject_monomial]
      split_ifs with h
      · rw [correction_monomial, h]
      · simp

omit [DecidableEq X] in
/-- The mixed relation on every actual tensor weight projection. -/
theorem positive_negative_project (μ ν : X) (i j : I)
    (z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    positive D.toSuperCartanDatum (fun l ↦ D.h l μ) i
      (negative D.toSuperCartanDatum j (weightProject D μ ν z)) =
    pi ^ (D.parity i * D.parity j).val •
      negative D.toSuperCartanDatum j
        (positive D.toSuperCartanDatum (fun l ↦ D.h l μ) i (weightProject D μ ν z)) +
    if i = j then qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i ν) •
      weightProject D μ ν z else 0 := by
  classical
  have h := congrArg (fun f ↦ f (weightProject D μ ν z))
    (positive_negative D.toSuperCartanDatum (fun l ↦ D.h l μ) i j)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  rw [h]
  congr 1
  split_ifs
  · exact congrArg (fun f ↦ f z) (correction_project D μ ν i)
  · rfl

end OddMath.CoveringQuantum.UDot.GenericTensor

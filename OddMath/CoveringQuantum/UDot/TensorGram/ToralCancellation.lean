/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.TensorPositive
import OddMath.CoveringQuantum.UDot.TensorGram.Reciprocal

/-!
# Toral cancellation for normalized positive-word Grams

Actual weight-labelled transport scalars cancel the tensor toral amplitudes.
The calculation retains root multidegrees without an independent-root assumption.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.ToralCancellation
open Coefficients PreF GenericVerma MixedGram PolarizationTransport
open TensorPositive BarDerivatives Reciprocal
variable {I X : Type*} [AddCommGroup X]
variable (D : RootDatum I X)

/-- Positive word shifts retain the actual root multidegree. -/
theorem shift_pos (w : List I) :
    shift D (pos w) = halfWeight D true (wordWeight w) := by
  induction w with
  | nil => simp [pos, shift]
  | cons i w ih =>
    simp only [pos, List.map_cons, shift, wordWeight_cons, halfWeight_add,
      halfWeight_single] at *
    rw [ih]

/-- A positive root word does not change the weight-block parity. -/
theorem parl_add_word (i : I) (ζ : X) (w : List I) :
    D.parl i (ζ + halfWeight D true (wordWeight w)) = D.parl i ζ := by
  induction w generalizing ζ with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, halfWeight_add, halfWeight_single, halfRoot, ite_true]
    rw [← add_assoc, ih, D.parl_add_α]

/-- The positive transport factor changes by the symmetric root bicharacter. -/
theorem genScalar_add_root (side : Bool) (i j : I) (ζ : X) :
    genScalar D side true i (ζ + D.α j) =
      qp Coefficients.q (D.dot i j) * genScalar D side true i ζ := by
  simp only [genScalar, ite_true, D.parl_add_α, map_add, D.h_α]
  rw [show D.d i * (D.h i ζ + D.a i j + 1) =
    D.dot i j + D.d i * (D.h i ζ + 1) by simp only [SuperCartanDatum.dot]; ring]
  rw [← qp_mul]
  ring

/-- Permuting letters does not change the root degree. -/
theorem wordWeight_perm {u v : List I} (h : u.Perm v) : wordWeight u = wordWeight v := by
  exact (h.map (fun i ↦ Finsupp.single i 1)).sum_eq

/-- Transport scalar invariance is proved by adjacent transpositions. -/
theorem wordScalar_perm (side : Bool) (ζ : X) {u v : List I} (h : u.Perm v) :
    wordScalar D side ζ (pos u) = wordScalar D side ζ (pos v) := by
  induction h with
  | nil => rfl
  | @cons i u v h ih =>
    simp only [pos, List.map_cons, wordScalar] at *
    rw [ih]
    congr 2
    exact congrArg (ζ + ·) ((shift_pos D u).trans
      ((congrArg (halfWeight D true) (wordWeight_perm h)).trans (shift_pos D v).symm))
  | swap i j w =>
    simp only [pos, List.map_cons, wordScalar, shift, halfRoot, ite_true]
    rw [← add_assoc, add_right_comm ζ (D.α i), ← add_assoc,
      add_right_comm ζ (D.α j)]
    rw [genScalar_add_root, genScalar_add_root, D.dot_comm i j]
    ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equality of ROOT multidegrees, not equality of their weight images, gives a permutation. -/
theorem perm_of_wordWeight_eq {u v : List I} (h : wordWeight u = wordWeight v) : u.Perm v := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  simpa only [wordWeight_apply] using congrArg (fun a ↦ a i) h

/-- The literal toral amplitude is permutation-invariant. -/
theorem amplitude_perm (s : Bool) (Λ : X) {u v : List I} (h : u.Perm v) :
    amplitude D s Λ u = amplitude D s Λ v :=
  (h.map (tensorToralScalar D s · Λ)).prod_eq

/-- Evaluation of a root monomial has the expected word recursion. -/
theorem monomialValue_cons (t : I → Coefficients.Ring) (i : I) (w : List I) :
    monomialValue t (wordWeight (i :: w)) = t i * monomialValue t (wordWeight w) := by
  simp only [wordWeight_cons, monomialValue]
  rw [Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _)]
  simp

/-- Exact one-letter cancellation, including the full shifted weight. -/
theorem scalar_step (Λ Μ : X) (s : Bool) (i : I) (w : List I) :
    genScalar D true true i (Λ - Μ + shift D (pos w)) *
      genScalar D false true i (Λ - Μ + shift D (pos w)) *
      tensorToralScalar D s i Λ * tensorToralScalar D (!s) i Λ =
    (D.pii pi i * qp Coefficients.q (2 * D.d i) *
      qp Coefficients.q (2 * D.d i * D.h i (halfWeight D true (wordWeight w)))) *
      bar (deformationParameter D Μ i) := by
  have hp : pi ^ (D.parl i (Λ - Μ)).val * D.pii pi i ^ (D.h i Λ).natAbs =
      D.pii pi i * D.pii pi i ^ (D.h i Μ).natAbs := by
    rw [← polarizationSign_eq_parl, polarizationSign]
    simp only [RootDatum.h, map_sub]
    rw [sub_eq_add_neg,
      tensor_pii_abs_add, Int.natAbs_neg]
    have hs : (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm _ 2, pow_mul, D.pii_sq pi pi_sq, one_pow]
    calc
      _ = D.pii pi i * D.pii pi i ^ (D.h i Μ).natAbs *
          (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 := by ring
      _ = _ := by rw [hs, mul_one]
  rw [shift_pos]
  simp only [genScalar, ite_true, Bool.false_eq_true, ite_false, one_mul,
    parl_add_word, tensorToralScalar, deformationParameter, map_mul, map_pow,
    barData.map_pii, qi_zpow, barData.map_qp, map_add, map_sub]
  cases s <;> simp only [Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true,
    ite_false, one_mul] <;>
    calc
      _ = (pi ^ (D.parl i (Λ - Μ)).val * D.pii pi i ^ (D.h i Λ).natAbs) *
          (qp Coefficients.q (D.d i * (D.h i Λ - D.h i Μ +
            D.h i (halfWeight D true (wordWeight w)) + 1)) *
           qp Coefficients.q (D.d i * (D.h i Λ - D.h i Μ +
            D.h i (halfWeight D true (wordWeight w)) + 1)) *
           qp Coefficients.q (-(D.d i * D.h i Λ)) *
           qp Coefficients.q (-(D.d i * D.h i Λ))) := by ring
      _ = _ := by
        rw [hp]
        simp only [qp_mul]
        rw [show D.d i * (D.h i Λ - D.h i Μ +
            D.h i (halfWeight D true (wordWeight w)) + 1) +
            D.d i * (D.h i Λ - D.h i Μ +
            D.h i (halfWeight D true (wordWeight w)) + 1) +
            -(D.d i * D.h i Λ) + -(D.d i * D.h i Λ) =
            2 * D.d i + 2 * D.d i * D.h i (halfWeight D true (wordWeight w)) +
            -(D.d i * (2 * D.h i Μ)) by ring]
        simp only [← qp_mul]
        ring

/-- All-word diagonal cancellation by induction on the original positive word. -/
theorem scalar_diagonal (Λ Μ : X) (s : Bool) (w : List I) :
    wordScalar D true (Λ - Μ) (pos w) * wordScalar D false (Λ - Μ) (pos w) *
      amplitude D s Λ w * amplitude D (!s) Λ w =
    topScale D w * bar (monomialValue (deformationParameter D Μ) (wordWeight w)) := by
  induction w with
  | nil => simp [pos, wordScalar, amplitude, topScale, monomialValue]
  | cons i w ih =>
    change (genScalar D true true i (Λ - Μ + shift D (pos w)) *
        wordScalar D true (Λ - Μ) (pos w)) *
      (genScalar D false true i (Λ - Μ + shift D (pos w)) *
        wordScalar D false (Λ - Μ) (pos w)) *
      (tensorToralScalar D s i Λ * amplitude D s Λ w) *
      (tensorToralScalar D (!s) i Λ * amplitude D (!s) Λ w) = _
    calc
      _ = (genScalar D true true i (Λ - Μ + shift D (pos w)) *
          genScalar D false true i (Λ - Μ + shift D (pos w)) *
          tensorToralScalar D s i Λ * tensorToralScalar D (!s) i Λ) *
        (wordScalar D true (Λ - Μ) (pos w) * wordScalar D false (Λ - Μ) (pos w) *
          amplitude D s Λ w * amplitude D (!s) Λ w) := by ring
      _ = _ := by
        rw [scalar_step, ih, topScale, monomialValue_cons, map_mul]
        ring

/-- Actual positive scalar cancellation for two words of equal ROOT multidegree.
No root-independence, dominance, or assumed scalar identity is needed. -/
theorem scalar_cancellation (Λ Μ : X) (s : Bool) (u v : List I)
    (huv : wordWeight u = wordWeight v) :
    wordScalar D true (Λ - Μ) (pos u) * wordScalar D false (Λ - Μ) (pos v) *
      amplitude D s Λ u * amplitude D (!s) Λ v =
    topScale D u * bar (monomialValue (deformationParameter D Μ) (wordWeight u)) := by
  have hp := perm_of_wordWeight_eq huv
  rw [← wordScalar_perm D false (Λ - Μ) hp, ← amplitude_perm D (!s) Λ hp]
  exact scalar_diagonal D Λ Μ s u

/-- The transported scalar is exactly the prefactor of the actual normalized reciprocal,
for either original coproduct at ζ = Λ - Μ. -/
theorem transported_scalar_cancellation (Λ Μ : X) (s : Bool) (u v : List I)
    (huv : wordWeight u = wordWeight v) :
    bar (wordScalar D true (Λ - Μ) (pos u) * wordScalar D false (Λ - Μ) (pos v) *
      amplitude D s Λ u * amplitude D (!s) Λ v) =
    bar (topScale D u) * monomialValue (deformationParameter D Μ) (wordWeight u) := by
  rw [scalar_cancellation D Λ Μ s u v huv, map_mul, bar_bar]

end OddMath.CoveringQuantum.UDot.ToralCancellation

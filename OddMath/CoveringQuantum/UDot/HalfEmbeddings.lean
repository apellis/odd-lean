/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaRepresentation

/-!
# Embeddings of the two halves in the modified covering quantum group

Over the generic covering ring, vacuum evaluation
in the actual highest-weight representation retracts the negative half map.
The positive half is treated using the scalar-bar-semilinear symmetry `omega`.
These are embeddings of the individual halves, not triangular injectivity.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
private theorem halfWeight_false (ν : I →₀ ℕ) :
    halfWeight D false ν = -halfWeight D true ν := by
  simp [halfWeight, halfRoot, Finsupp.sum, Finset.sum_neg_distrib]

namespace GenericVerma

/-- Evaluation on the highest-weight vacuum, on the unital envelope. -/
def vacuumEval (μ : X) :
    CoveringUDot Coefficients.Ring D Coefficients.q pi →ₗ[Coefficients.Ring]
      D.serreF Coefficients.q pi where
  toFun x := representation D μ x 1
  map_add' x y := by simp
  map_smul' c x := by simp

/-- A negative word applied to the vacuum recovers the actual Serre word. -/
theorem vacuumEval_halfWord (μ : X) (w : List I) :
    vacuumEval D μ (halfWord D Coefficients.q pi false w μ) =
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  induction w with
  | nil =>
    change representation D μ (one D Coefficients.q pi μ) 1 = _
    rw [representation_one]
    rw [← map_one (D.toSerreF Coefficients.q pi), weightProject_mk]
    change D.toSerreF Coefficients.q pi
      (weightProjectFree D μ μ (monomial Coefficients.Ring [])) = _
    simp only [weightProjectFree_monomial, wordWeight_nil, halfWeight_zero, sub_self,
      ite_true]
  | cons i w ih =>
    change representation D μ
      (F D Coefficients.q pi i (μ + halfWeight D false (wordWeight w)) *
        halfWord D Coefficients.q pi false w μ) 1 = _
    rw [map_mul, Module.End.mul_apply]
    change representation D μ (F D Coefficients.q pi i _) (vacuumEval D μ _) = _
    rw [ih, representation_F, weightProject_mk, weightProjectFree_monomial]
    rw [halfWeight_false]
    simp [monomial_cons]

/-- The negative half map is retracted by evaluation at its right weight. -/
theorem vacuumEval_halfMap (μ : X) (x : D.serreF Coefficients.q pi) :
    vacuumEval D μ (halfMap D Coefficients.q pi false μ x) = x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w => rw [halfMap_monomial, vacuumEval_halfWord]
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

end GenericVerma

/-- A linear retraction of the existing negative map into the nonunital modified algebra. -/
def negativeRetraction (μ : X) :
    modified D Coefficients.q pi →ₗ[Coefficients.Ring] D.serreF Coefficients.q pi :=
  (GenericVerma.vacuumEval D μ).comp (modified D Coefficients.q pi).toSubmodule.subtype

/-- The actual negative half map has a checked left inverse at every right weight. -/
theorem negativeRetraction_half (μ : X) :
    Function.LeftInverse (negativeRetraction D μ) (negativeHalf D Coefficients.q pi μ) :=
  GenericVerma.vacuumEval_halfMap D μ

/-- Injectivity of the existing negative half map over the generic covering ring. -/
theorem negativeHalf_injective (μ : X) :
    Function.Injective (negativeHalf D Coefficients.q pi μ) :=
  (negativeRetraction_half D μ).injective

namespace GenericVerma

/-- The existing semilinear symmetry exchanges signed words and negates the right weight. -/
theorem omega_halfWord (μ : X) (w : List I) :
    omega D Coefficients.q pi bar barData (halfWord D Coefficients.q pi true w μ) =
      halfWord D Coefficients.q pi false w (-μ) := by
  induction w with
  | nil => exact omega_one barData μ
  | cons i w ih =>
    change omega D Coefficients.q pi bar barData
      (E D Coefficients.q pi i (μ + halfWeight D true (wordWeight w)) *
        halfWord D Coefficients.q pi true w μ) = _
    rw [map_mul, omega_E, ih]
    simp only [halfWord, halfGen, Bool.false_eq_true, ite_false, halfWeight_false, neg_add]

/-- Vacuum evaluation after `omega` is scalar-bar-semilinear, not linear. -/
def positiveVacuum (μ : X) :
    CoveringUDot Coefficients.Ring D Coefficients.q pi →ₛₗ[bar]
      D.serreF Coefficients.q pi where
  toFun x := vacuumEval D (-μ) (omega D Coefficients.q pi bar barData x)
  map_add' x y := by simp
  map_smul' c x := by simp only [omega_smul, map_smul]

/-- Positive words are recovered with coefficient conjugation by the scalar bar. -/
theorem positiveVacuum_halfWord (μ : X) (w : List I) :
    positiveVacuum D μ (halfWord D Coefficients.q pi true w μ) =
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  change vacuumEval D (-μ) (omega D Coefficients.q pi bar barData _) = _
  rw [omega_halfWord, vacuumEval_halfWord]

/-- Scalar conjugation on the actual Serre half, constructed using the weight-zero
vacuum and `omega`. The word and scalar formulas characterize it without a new presentation. -/
def halfBar : D.serreF Coefficients.q pi →ₛₗ[bar] D.serreF Coefficients.q pi where
  toFun x := positiveVacuum D 0 (halfMap D Coefficients.q pi true 0 x)
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem halfBar_monomial (w : List I) :
    halfBar D (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  change positiveVacuum D 0 (halfMap D Coefficients.q pi true 0 _) = _
  rw [halfMap_monomial, positiveVacuum_halfWord]

/-- The constructed scalar conjugation is involutive. -/
theorem halfBar_halfBar (x : D.serreF Coefficients.q pi) :
    halfBar D (halfBar D x) = x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w => rw [halfBar_monomial, halfBar_monomial]
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, map_smulₛₗ, bar_bar, hx]

/-- The semilinear evaluation has the same scalar conjugation at every right weight. -/
theorem positiveVacuum_halfMap (μ : X) (x : D.serreF Coefficients.q pi) :
    positiveVacuum D μ (halfMap D Coefficients.q pi true μ x) = halfBar D x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w => rw [halfMap_monomial, positiveVacuum_halfWord, halfBar_monomial]
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, map_smulₛₗ, hx]

end GenericVerma

/-- Two scalar-bar-semilinear maps give a linear retraction of the existing positive half. -/
def positiveRetraction (μ : X) :
    modified D Coefficients.q pi →ₗ[Coefficients.Ring] D.serreF Coefficients.q pi where
  toFun x := GenericVerma.halfBar D (GenericVerma.positiveVacuum D μ x)
  map_add' x y := by simp
  map_smul' c x := by
    simp only [NonUnitalSubalgebra.coe_smul, map_smulₛₗ, bar_bar, RingHom.id_apply]

/-- The actual positive half map has a checked linear left inverse at every right weight. -/
theorem positiveRetraction_half (μ : X) :
    Function.LeftInverse (positiveRetraction D μ) (positiveHalf D Coefficients.q pi μ) := by
  intro x
  change GenericVerma.halfBar D
    (GenericVerma.positiveVacuum D μ (halfMap D Coefficients.q pi true μ x)) = x
  rw [GenericVerma.positiveVacuum_halfMap, GenericVerma.halfBar_halfBar]

/-- Injectivity of the existing positive half map over the generic covering ring. -/
theorem positiveHalf_injective (μ : X) :
    Function.Injective (positiveHalf D Coefficients.q pi μ) :=
  (positiveRetraction_half D μ).injective

end OddMath.CoveringQuantum.UDot

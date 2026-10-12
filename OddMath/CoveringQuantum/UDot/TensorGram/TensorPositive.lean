/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.TensorGram.Words

/-!
# All-positive tensor actions

The exact all-positive tensor action and its transported Gram scalar require
no root-independence, limit or toral cancellation hypothesis.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.TensorPositive
open Coefficients PreF TensorProduct GenericVerma MixedGram PolarizationTransport
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X)

/-- All letters are the original positive generators. -/
def pos (w : List I) : List (Bool × I) := w.map (fun i ↦ (true, i))

/-- Exact toral amplitude, with repetitions counted in the word. -/
def amplitude (s : Bool) (Λ : X) (w : List I) : Coefficients.Ring :=
  (w.map (fun i ↦ tensorToralScalar D s i Λ)).prod

variable (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

/-- The annihilating coproduct branch vanishes on the highest vector, even
when the second factor is an arbitrary free-algebra vector. -/
theorem E_highest (s : Bool) (i : I) (y : PreF Coefficients.Ring I) :
    tensorE D hD Λ Μ s i
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] project D hD Μ y) =
      tensorToralScalar D s i Λ •
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          project D hD Μ (θ Coefficients.Ring i * y)) := by
  have h := step_value D hD Λ Μ s true i (1, y)
  simpa [step, listValue, pairValue, project, freeTwist, lowerFree,
    freeWeight_one, tensorChevalley, smul_tmul] using h.symm

/-- Exact all-positive collapse for either original coproduct. -/
theorem wordAction_pos (s : Bool) (w : List I) :
    wordAction D hD Λ Μ s (pos w) (vac D hD Λ Μ) =
      amplitude D s Λ w •
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          project D hD Μ (monomial Coefficients.Ring w)) := by
  induction w with
  | nil => simp [pos, wordAction, amplitude, vac, project]
  | cons i w ih =>
    change tensorE D hD Λ Μ s i
      (wordAction D hD Λ Μ s (pos w) (vac D hD Λ Μ)) = _
    rw [ih, map_smul, E_highest, smul_smul]
    simp only [amplitude, List.map_cons, List.prod_cons, monomial_cons]
    rw [mul_comm]

/-- Collapse of the genuine weight-labelled modified-algebra action. -/
theorem algebraWord_pos_action (s : Bool) (w : List I) :
    tensorRepresentation D hD Λ Μ s (algebraWord D (Λ - Μ) (pos w)).val
      (vac D hD Λ Μ) =
      amplitude D s Λ w •
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          project D hD Μ (monomial Coefficients.Ring w)) := by
  rw [algebraWord_action]
  exact wordAction_pos D hD Λ Μ s w

/-- The lowest form is the normalized Verma form, hence the actual word
polynomial evaluated at the lowest weight's deformation parameter. -/
theorem lowest_word (hΜ : ∀ i, 0 ≤ D.h i Μ) (u v : List I) :
    lowestPolarization D hD Μ hΜ
      (project D hD Μ (monomial Coefficients.Ring u))
      (project D hD Μ (monomial Coefficients.Ring v)) =
      MvPolynomial.eval (deformationParameter D Μ)
        (wordPolynomial D u (monomial Coefficients.Ring v)) := by
  rw [lowest_polynomial, halfPolynomial_word]

/-- Actual tensor Gram before coefficient-bar transport; the two coproducts
can be chosen independently. -/
theorem tensor_gram_pos (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s t : Bool) (u v : List I) :
    tensorPolarization D hD Λ Μ hΛ hΜ
      (wordAction D hD Λ Μ s (pos u) (vac D hD Λ Μ))
      (wordAction D hD Λ Μ t (pos v) (vac D hD Λ Μ)) =
      amplitude D s Λ u * amplitude D t Λ v *
        MvPolynomial.eval (deformationParameter D Μ)
          (wordPolynomial D u (monomial Coefficients.Ring v)) := by
  rw [wordAction_pos, wordAction_pos, LinearMap.map_smul₂, LinearMap.map_smul,
    tensorPolarization_tmul]
  simp only [integrablePolarization_highest, one_mul, lowest_word, smul_eq_mul, mul_assoc]

/-- Exact transported Gram on the original modified algebra. The outer bar
covers every scalar, including the evaluated word polynomial. -/
theorem modifiedGram_pos (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    modifiedGram D hD Λ Μ hΛ hΜ s
      (algebraWord D (Λ - Μ) (pos u)) (algebraWord D (Λ - Μ) (pos v)) =
      bar (wordScalar D true (Λ - Μ) (pos u) *
        wordScalar D false (Λ - Μ) (pos v) *
        amplitude D s Λ u * amplitude D (!s) Λ v *
        MvPolynomial.eval (deformationParameter D Μ)
          (wordPolynomial D u (monomial Coefficients.Ring v))) := by
  change gram D hD Λ Μ hΛ hΜ s (algebraWord D (Λ - Μ) (pos u)).val
    (algebraWord D (Λ - Μ) (pos v)).val = _
  rw [gram_apply]
  have hl := word_transport D true (Λ - Μ) (pos u)
  have hr := word_transport D false (Λ - Μ) (pos v)
  simp only [ite_true, Bool.false_eq_true, ite_false] at hl hr
  rw [hl, hr]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, algebraWord_action,
    tensor_gram_pos, mul_assoc, mul_left_comm]

end OddMath.CoveringQuantum.UDot.TensorPositive

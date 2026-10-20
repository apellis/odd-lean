/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.FiniteGram

/-!
# Weight-labelled transport of tensor Gram words

Transport scalars retain the original composable weights and multiplication
order, rather than just word lengths.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.PolarizationTransport
open Coefficients PreF TensorProduct GenericVerma MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
/-- Weight-labelled generator factors, not word length. -/
def genScalar (side positive : Bool) (i : I) (μ : X) : Coefficients.Ring :=
  if positive then
    (if side then 1 else pi ^ (D.parl i μ).val) *
      qp Coefficients.q (D.d i * (D.h i μ + 1))
  else
    (if side then pi ^ (D.parl i μ).val else 1) *
      qp Coefficients.q (-(D.d i * (D.h i μ - 1)))

theorem gen_transport (side positive : Bool) (i : I) (μ : X) :
    (if side then left D else right D) (halfGen D Coefficients.q pi positive i μ) =
      genScalar D side positive i μ • halfGen D Coefficients.q pi positive i μ := by
  cases side <;> cases positive <;> simp [genScalar, halfGen]

omit [DecidableEq I] [DecidableEq X] in
def wordScalar (side : Bool) (ζ : X) : List (Bool × I) → Coefficients.Ring
  | [] => 1
  | g :: w => genScalar D side g.1 g.2 (ζ + shift D w) * wordScalar side ζ w

/-- Genuine quotient equality, with composable original weights. -/
theorem word_transport (side : Bool) (ζ : X) (w : List (Bool × I)) :
    (if side then left D else right D) (algebraWord D ζ w).val =
      wordScalar D side ζ w • (algebraWord D ζ w).val := by
  induction w with
  | nil => cases side <;> simp [algebraWord, wordScalar]
  | cons g w ih =>
    change (if side then left D else right D)
      (halfGen D Coefficients.q pi g.1 g.2 (ζ + shift D w) * (algebraWord D ζ w).val) = _
    rw [map_mul, gen_transport, ih, smul_mul_smul_comm]
    rfl

variable (Λ Μ : X)

/-- The original two-branch action is retained on every generator block. -/
theorem generator_action (side s positive : Bool) (i : I) (μ : X) :
    tensorRepresentation D Λ Μ s
      ((if side then left D else right D) (halfGen D Coefficients.q pi positive i μ)) =
    genScalar D side positive i μ •
      (tensorChevalley D Λ Μ s positive i * tensorProject D Λ Μ μ) := by
  rw [gen_transport, map_smul]
  cases positive <;> simp [halfGen, tensorChevalley, tensorEBlock]

/-- Explicit finite transported formula, still allowing arbitrary mixed words.
The coefficient bar is applied to the FULL evaluated expression. -/
def wordFormula (s : Bool) (u v : List (Bool × I)) : Coefficients.Ring :=
  bar (wordScalar D true (Λ - Μ) u * wordScalar D false (Λ - Μ) v *
    MvPolynomial.eval (jointParameter D Λ Μ) (gramPolynomial D Λ Μ s (!s) u v))

theorem word_gram_formula (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List (Bool × I)) :
    modifiedGram D Λ Μ hΛ hΜ s (algebraWord D (Λ - Μ) u) (algebraWord D (Λ - Μ) v) =
      wordFormula D Λ Μ s u v := by
  change gram D Λ Μ hΛ hΜ s (algebraWord D (Λ - Μ) u).val
    (algebraWord D (Λ - Μ) v).val = _
  rw [gram_apply]
  have hl := word_transport D true (Λ - Μ) u
  have hr := word_transport D false (Λ - Μ) v
  simp only [ite_true, Bool.false_eq_true, ite_false] at hl hr
  rw [hl, hr]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, algebraWord_action,
    mixed_gram_formula, wordFormula, vac, mul_assoc, mul_left_comm]

/-- Evaluated formula independent of actual modified representatives. -/
theorem word_formula_invariant (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u u' v v' : List (Bool × I))
    (hu : algebraWord D (Λ - Μ) u = algebraWord D (Λ - Μ) u')
    (hv : algebraWord D (Λ - Μ) v = algebraWord D (Λ - Μ) v') :
    wordFormula D Λ Μ s u v = wordFormula D Λ Μ s u' v' := by
  rw [← word_gram_formula D Λ Μ hΛ hΜ, ← word_gram_formula D Λ Μ hΛ hΜ, hu, hv]

end OddMath.CoveringQuantum.UDot.PolarizationTransport

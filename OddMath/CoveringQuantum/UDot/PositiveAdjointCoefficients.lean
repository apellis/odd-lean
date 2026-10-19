/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.AdjointCoefficients
import OddMath.SKM.CoveringDatum

/-!
# Physical positive left-cons and adjoint coefficients

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 2: the algebraic coefficient
step for positive input lists. Physical lists evaluate in the same order.
Simultaneous reversal is used only on the scalar form of two positive words,
not on modified elements or on a mixed pair. Colours may be infinite, without
bar consistency. This is not the graphical iff.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- Simultaneously reversing two positive lists preserves the scalar form.
This does not identify the corresponding modified-algebra elements. -/
theorem sesquilinearForm_positive_reverse (μ : X) (a b : List I) :
    sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a.reverse)))
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b.reverse))) =
    sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)))
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) := by
  rw [sesquilinearForm_reversed_words, sesquilinearForm_positiveHalf,
    GenericVerma.halfBar_monomial]

omit [DecidableEq I] [DecidableEq X] in
/-- The right region of a cup attached at physical bottom left. -/
theorem positive_word_physical_weight (μ : X) (a : List I) :
    OddMath.SKM.wt D.toSKM μ (a.map fun i => (true, i)) =
      μ + halfWeight D true (wordWeight a) := by
  induction a with
  | nil => simp
  | cons i a ih =>
    simp only [List.map_cons, OddMath.SKM.wt_cons, OddMath.SKM.sh, ite_true,
      RootDatum.toSKM_α, ih, wordWeight_cons, halfWeight_add, halfWeight_single,
      halfRoot]
    abel

/-- Multiplication by E adds a letter at physical left, without reversal. -/
theorem positiveHalf_leftCons (i : I) (μ : X) (a : List I) :
    (⟨E D Coefficients.q pi i (μ + halfWeight D true (wordWeight a)),
      E_mem_modified D Coefficients.q pi i _⟩ : modified D Coefficients.q pi) *
      positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)) =
    positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (i :: a))) := by
  apply Subtype.ext
  change E D Coefficients.q pi i _ * halfMap D Coefficients.q pi true μ _ =
    halfMap D Coefficients.q pi true μ _
  simp only [halfMap_monomial, halfWord, halfGen, ite_true]

/-- BE2 Theorem 10.3 Claim 2, physical left-cons algebraic coefficient step.
The physical cup region is ν, and F has right idempotent ν + αᵢ. Its degree
shift is δ = dᵢ(1+hᵢν), with no parity factor. The positive RHS uses the
unchanged reversed-word coordinates of the positive-family theorem.
No mixed-word reversal, graphical normalization, or family bijection is asserted.
Colours may be infinite, without bar consistency. -/
theorem sesquilinearForm_positive_leftCons_bent_coeff
    (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) (μ : X) (a b : List I) (z : ℤ) :
    let ν := OddMath.SKM.wt D.toSKM μ (a.map fun j => (true, j))
    (signLaurent σ hσ (sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)))
      (⟨F D Coefficients.q pi i (ν + D.α i),
        F_mem_modified D Coefficients.q pi i (ν + D.α i)⟩ *
        positiveHalf D Coefficients.q pi μ
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))))).coeff z =
    (signLaurent σ hσ (sesquilinearForm D
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (i :: a).reverse)))
      (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b.reverse))))).coeff
      (z - D.d i * (1 + D.h i ν)) := by
  dsimp only
  rw [sesquilinearForm_E_bent_coeff, positive_word_physical_weight,
    positiveHalf_leftCons, sesquilinearForm_positive_reverse]

end OddMath.CoveringQuantum.UDot.GenericTensor

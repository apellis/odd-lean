/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldTriplePolynomial

/-! # The normalized repeated-outer OLD braid on direct induction

Brundan–Ellis (1.9): the two independently chosen direct crossing paths,
with the negative equal crossing in each, differ by the ordered correction
in the original parameter family Sc. The literal OLD quotient supplies
the braid difference. No braid, polynomial-naturality or comparison
premise is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u

private theorem three_transform_composition
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F₀ F₁ F₂ F₃ : C ⥤ E}
    [F₀.Additive] [F₀.Linear k] [IsSuperfunctor k F₀]
    [F₁.Additive] [F₁.Linear k] [IsSuperfunctor k F₁]
    [F₂.Additive] [F₂.Linear k] [IsSuperfunctor k F₂]
    [F₃.Additive] [F₃.Linear k] [IsSuperfunctor k F₃]
    {p q r : ZMod 2}
    {a : ∀ s, F₀.obj s ⟶ F₁.obj s} {b : ∀ s, F₁.obj s ⟶ F₂.obj s}
    {c : ∀ s, F₂.obj s ⟶ F₃.obj s}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k q b) (hc : IsSupernatural k r c)
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear ha N w ∘ₗ transformLinear hb N w ∘ₗ transformLinear hc N w =
      sign k (p * q + (p + q) * r) • transformLinear ((ha.comp hb).comp hc) N w := by
  rw [← LinearMap.comp_assoc, transformLinear_comp, LinearMap.smul_comp,
    transformLinear_comp, smul_smul, ← sign_add]

private theorem repeated_degree (p q : ZMod 2) : (p * q + p * p) + q * p = p := by
  rcases parity_eq_zero_or_one p with hp | hp <;>
    rcases parity_eq_zero_or_one q with hq | hq <;> rw [hp, hq] <;> decide

private theorem repeated_sign (p q : ZMod 2) :
    (p * q) * (p * p) + (p * q + p * p) * (q * p) = p * q := by
  rcases parity_eq_zero_or_one p with hp | hp <;>
    rcases parity_eq_zero_or_one q with hq | hq <;> rw [hp, hq] <;> decide

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed suffix-first minus prefix-first paths, with both equal crossings negative. -/
def oldDirectMixedBraid (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :=
  transformLinear (tripleSuffix_supernatural D Sc cutoff i j i) N w ∘ₗ
    (-transformLinear (triplePrefix_supernatural D Sc cutoff i i j) N w) ∘ₗ
      transformLinear (tripleSuffix_supernatural D Sc cutoff i i j) N w -
  transformLinear (triplePrefix_supernatural D Sc cutoff i j i) N w ∘ₗ
    (-transformLinear (tripleSuffix_supernatural D Sc cutoff j i i) N w) ∘ₗ
      transformLinear (triplePrefix_supernatural D Sc cutoff j i i) N w

/-- The whole normalized direct OLD braid difference is the original-parameter ordered correction. -/
theorem oldDirectMixedBraid_polynomial {i j : I} (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D (parameterTwist D Sc) cutoff) (SVec k))
    (w : OldCategory D (parameterTwist D Sc) cutoff) :
    oldDirectMixedBraid D (parameterTwist D Sc) cutoff i j N w =
      tripleDotCorrectionPolynomial D Sc i j
        (transformLinear (tripleFirstDot_supernatural D (parameterTwist D Sc) cutoff i j) N w)
        (transformLinear (tripleMiddleDot_supernatural D (parameterTwist D Sc) cutoff i j) N w)
        (transformLinear (tripleLastDot_supernatural D (parameterTwist D Sc) cutoff i j) N w) := by
  rw [oldTriplePolynomial_operator D Sc cutoff hij N w]
  unfold oldDirectMixedBraid
  simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_sub_neg]
  rw [three_transform_composition, three_transform_composition]
  have hdL := repeated_degree (D.parity i) (D.parity j)
  have hdR : (D.parity j * D.parity i + D.parity i * D.parity i) +
      D.parity i * D.parity j = D.parity i := by
    simpa only [mul_comm] using hdL
  have hsL := repeated_sign (D.parity i) (D.parity j)
  have hsR : (D.parity j * D.parity i) * (D.parity i * D.parity i) +
      (D.parity j * D.parity i + D.parity i * D.parity i) * (D.parity i * D.parity j) =
      D.parity i * D.parity j := by
    simpa only [mul_comm] using hsL
  rw [hsL, hsR]
  erw [← smul_sub]
  apply hom_ext
  intro s g z
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    transformLinear_tensor, transformLinear_tensor, transformLinear_tensor]
  simp only [hdL, hdR]
  change sign k (D.parity i * D.parity j) •
      (inductionEndTensorEval (tripleAppend D (parameterTwist D Sc) cutoff i j i) N w s
          (twist k (D.parity i) g) z
          ((triplePrefix D (parameterTwist D Sc) cutoff i j i s ≫
            tripleSuffix D (parameterTwist D Sc) cutoff j i i s) ≫
              triplePrefix D (parameterTwist D Sc) cutoff j i i s) -
        inductionEndTensorEval (tripleAppend D (parameterTwist D Sc) cutoff i j i) N w s
          (twist k (D.parity i) g) z
          ((tripleSuffix D (parameterTwist D Sc) cutoff i j i s ≫
            triplePrefix D (parameterTwist D Sc) cutoff i i j s) ≫
              tripleSuffix D (parameterTwist D Sc) cutoff i i j s)) = _
  rw [← map_sub]
  have hs := tripleCross_braid_correction D (parameterTwist D Sc) cutoff i j hij s
  simp only [← Category.assoc] at hs
  rw [hs]
  rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

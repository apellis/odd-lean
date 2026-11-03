/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTriplePolynomialMaps

/-! # Corrected three-path relations under balanced induction

Brundan–Ellis (1.9): transport the literal repeated-outer source coefficient
relation across three possibly different composite functors. This generic
intermediate takes that source coefficient equation explicitly. Concrete
OLD and stored-target actions supply it from the proved quotient relation;
no such premise belongs to the final action field.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem corrected_three_linear_comp
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

private theorem corrected_degree (p q : ZMod 2) : (p * q + p * p) + q * p = p := by
  rcases parity_eq_zero_or_one p with hp | hp <;>
    rcases parity_eq_zero_or_one q with hq | hq <;> rw [hp, hq] <;> decide

private theorem corrected_sign (p q : ZMod 2) :
    (p * q) * (p * p) + (p * q + p * p) * (q * p) = p * q := by
  rcases parity_eq_zero_or_one p with hp | hp <;>
    rcases parity_eq_zero_or_one q with hq | hq <;> rw [hp, hq] <;> decide

private theorem corrected_total
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hγ N).total w = transformLinear hγ N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem corrected_path_total
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M A B : Superfunctor k C (SVec k)}
    (f₀ : M ⟶ A) (f₁ : End A) (f₂ : A ⟶ M)
    (g₀ : M ⟶ B) (g₁ : End B) (g₂ : B ⟶ M) (w : C) :
    (f₀ ≫ (-f₁) ≫ f₂ - g₀ ≫ (-g₁) ≫ g₂).total w =
      f₂.total w ∘ₗ (-f₁.total w) ∘ₗ f₀.total w -
        g₂.total w ∘ₗ (-g₁.total w) ∘ₗ g₀.total w := by
  have hsub {P Q : Superfunctor k C (SVec k)} (f g : P ⟶ Q) :
      (f - g).total w = f.total w - g.total w := by
    simp only [SuperNatTrans.total, Superfunctor.sub_app]
    abel
  have hneg {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) :
      (-f).total w = -f.total w := by
    simp only [SuperNatTrans.total, Superfunctor.neg_app, neg_add]
  simp only [hsub, Superfunctor.comp_total, hneg]
  rfl

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F₀ F₁ F₂ : C ⥤ E)
  [F₀.Additive] [F₀.Linear k] [IsSuperfunctor k F₀]
  [F₁.Additive] [F₁.Linear k] [IsSuperfunctor k F₁]
  [F₂.Additive] [F₂.Linear k] [IsSuperfunctor k F₂]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F₀.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)
  {α₀ : ∀ s, F₀.obj s ⟶ F₂.obj s} {α₁ : ∀ s, F₂.obj s ⟶ F₂.obj s}
  {α₂ : ∀ s, F₂.obj s ⟶ F₀.obj s} {β₀ : ∀ s, F₀.obj s ⟶ F₁.obj s}
  {β₁ : ∀ s, F₁.obj s ⟶ F₁.obj s} {β₂ : ∀ s, F₁.obj s ⟶ F₀.obj s}
  (hα₀ : IsSupernatural k (D.parity i * D.parity j) α₀)
  (hα₁ : IsSupernatural k (D.parity i * D.parity i) α₁)
  (hα₂ : IsSupernatural k (D.parity j * D.parity i) α₂)
  (hβ₀ : IsSupernatural k (D.parity j * D.parity i) β₀)
  (hβ₁ : IsSupernatural k (D.parity i * D.parity i) β₁)
  (hβ₂ : IsSupernatural k (D.parity i * D.parity j) β₂)
  (hsource : ∀ s, (α₀ s ≫ α₁ s ≫ α₂ s) - (β₀ s ≫ β₁ s ≫ β₂ s) =
    tripleDotCorrectionPolynomial D (parameterTwist D Sc) (R := End (F₀.obj s)) i j (c s) (b s) (a s))

include hα₀ hα₁ hα₂ hβ₀ hβ₁ hβ₂ hsource in
private theorem corrected_linear_paths (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear hβ₀ N w ∘ₗ (-transformLinear hβ₁ N w) ∘ₗ transformLinear hβ₂ N w -
      transformLinear hα₀ N w ∘ₗ (-transformLinear hα₁ N w) ∘ₗ transformLinear hα₂ N w =
    tripleDotCorrectionPolynomial D Sc i j
      (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w) := by
  rw [transformLinear_triplePolynomial_eq F₀ D Sc i j ha hb hc hij N w]
  simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_sub_neg]
  rw [corrected_three_linear_comp, corrected_three_linear_comp]
  have hdL := corrected_degree (D.parity i) (D.parity j)
  have hdR : (D.parity j * D.parity i + D.parity i * D.parity i) +
      D.parity i * D.parity j = D.parity i := by
    simpa only [mul_comm] using hdL
  have hsL := corrected_sign (D.parity i) (D.parity j)
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
      (inductionEndTensorEval F₀ N w s (twist k (D.parity i) g) z ((α₀ s ≫ α₁ s) ≫ α₂ s) -
        inductionEndTensorEval F₀ N w s (twist k (D.parity i) g) z ((β₀ s ≫ β₁ s) ≫ β₂ s)) = _
  rw [← map_sub]
  have hs := hsource s
  simp only [← Category.assoc] at hs
  rw [hs]
  rfl

include hsource in
/-- The entire corrected induction braid, with its literal source coefficient equation. -/
theorem transformComponent_corrected_braid (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    (show End (induced F₀ N) from transformComponent hβ₂ N ≫ (-transformComponent hβ₁ N) ≫ transformComponent hβ₀ N) -
      (show End (induced F₀ N) from transformComponent hα₂ N ≫ (-transformComponent hα₁ N) ≫ transformComponent hα₀ N) =
    tripleDotCorrectionPolynomial D Sc (R := End (induced F₀ N)) i j
      (transformComponent ha N) (transformComponent hb N) (transformComponent hc N) := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F₀ N) →ₐ[k] Module.End k ((induced F₀ N).obj w) :=
    (svecEndEvaluation ((induced F₀ N).obj w)).comp (supernaturalEndEvaluation (induced F₀ N) w)
  change _ = ev (tripleDotCorrectionPolynomial D Sc (R := End (induced F₀ N)) i j
    (transformComponent ha N) (transformComponent hb N) (transformComponent hc N))
  rw [tripleDotCorrectionPolynomial_map, corrected_path_total]
  change _ = tripleDotCorrectionPolynomial D Sc (R := Module.End k ((induced F₀ N).obj w)) i j
    ((transformComponent ha N).total w) ((transformComponent hb N).total w) ((transformComponent hc N).total w)
  simp only [corrected_total]
  exact corrected_linear_paths F₀ F₁ F₂ D Sc i j ha hb hc
    hα₀ hα₁ hα₂ hβ₀ hβ₁ hβ₂ hsource hij N w

end OddMath.QuiverHecke.ELVOld.BalancedInduction

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Three-path relations under balanced induction

Brundan–Ellis (1.9): the three crossing parities occur in reverse order
on the two sides of a multicolour braid. Their superopposite composition
signs agree. This intermediate transport lemma takes the literal source
path equation; concrete OLD specializations supply it from the quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem multicolour_transform_total
    {k C A : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hγ M).total w = transformLinear hγ M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (T₀ T₁ T₂ T₃ T₄ T₅ : C ⥤ A)
  [T₀.Additive] [T₀.Linear k] [IsSuperfunctor k T₀]
  [T₁.Additive] [T₁.Linear k] [IsSuperfunctor k T₁]
  [T₂.Additive] [T₂.Linear k] [IsSuperfunctor k T₂]
  [T₃.Additive] [T₃.Linear k] [IsSuperfunctor k T₃]
  [T₄.Additive] [T₄.Linear k] [IsSuperfunctor k T₄]
  [T₅.Additive] [T₅.Linear k] [IsSuperfunctor k T₅]
  {p q r : ZMod 2}
  {α₀ : ∀ s, T₀.obj s ⟶ T₁.obj s} {α₁ : ∀ s, T₁.obj s ⟶ T₂.obj s}
  {α₂ : ∀ s, T₂.obj s ⟶ T₃.obj s} {β₀ : ∀ s, T₀.obj s ⟶ T₄.obj s}
  {β₁ : ∀ s, T₄.obj s ⟶ T₅.obj s} {β₂ : ∀ s, T₅.obj s ⟶ T₃.obj s}
  (hα₀ : IsSupernatural k p α₀) (hα₁ : IsSupernatural k q α₁)
  (hα₂ : IsSupernatural k r α₂) (hβ₀ : IsSupernatural k r β₀)
  (hβ₁ : IsSupernatural k q β₁) (hβ₂ : IsSupernatural k p β₂)

/-- The two reversed three-map paths have the same superopposite sign. -/
theorem transformComponent_multicolour_braid
    (hb : ∀ s, α₀ s ≫ α₁ s ≫ α₂ s = β₀ s ≫ β₁ s ≫ β₂ s)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hα₂ M ≫ transformComponent hα₁ M ≫ transformComponent hα₀ M =
      transformComponent hβ₂ M ≫ transformComponent hβ₁ M ≫ transformComponent hβ₀ M := by
  rw [transformComponent_comp hα₀ hα₁, Linear.comp_smul,
    transformComponent_comp (hα₀.comp hα₁) hα₂,
    transformComponent_comp hβ₀ hβ₁, Linear.comp_smul,
    transformComponent_comp (hβ₀.comp hβ₁) hβ₂,
    smul_smul, smul_smul, ← sign_add, ← sign_add]
  have hs : p * q + (p + q) * r = r * q + (r + q) * p := by ring
  rw [hs]
  congr 1
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  have hp : (p + q) + r = (r + q) + p := by ring
  have he : (fun s => (α₀ s ≫ α₁ s) ≫ α₂ s) =
      (fun s => (β₀ s ≫ β₁ s) ≫ β₂ s) := by
    funext s
    simpa only [Category.assoc] using hb s
  rw [multicolour_transform_total, multicolour_transform_total]
  apply hom_ext
  intro s a b
  simp only [transformLinear_tensor, ← hp]
  rw [← congrFun he s]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

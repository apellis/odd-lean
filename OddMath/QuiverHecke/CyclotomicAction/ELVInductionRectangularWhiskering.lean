/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Rectangular transformation squares for induction composition

Brundan–Ellis (1.9), the changing-category braid comparisons: the chosen
induction-composition isomorphisms intertwine the independent inner and
outer source transformations, with distinct source and target functors.
These entire module-map squares retain the supernaturality kernel twists.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]

private theorem rectangular_square_of_total
    {M₀ M₁ N₀ N₁ : Superfunctor k B (SVec k)}
    (f : M₀ ⟶ M₁) (e₀ : M₀ ⟶ N₀) (e₁ : M₁ ⟶ N₁) (g : N₀ ⟶ N₁)
    (h : ∀ w, SVec.toLinearMap (e₁.total w) ∘ₗ SVec.toLinearMap (f.total w) =
      SVec.toLinearMap (g.total w) ∘ₗ SVec.toLinearMap (e₀.total w)) :
    f ≫ e₁ = e₀ ≫ g := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  exact LinearMap.congr_fun (h w) x

private theorem rectangular_induction_map_total
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {M N : Superfunctor k A (SVec k)} {p : ZMod 2} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) _ _ p) (w : B) :
    ((induction K).map f).total w = mapComponent K f p w := by
  have hm := Supercategory.map_mem (induction K) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

private theorem rectangular_transform_total
    {J J' : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J'.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable (J J' : C ⥤ A)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The actual outer induction maps the inner transformation to its source whisker. -/
theorem inductionComp_inner_transform {p : ZMod 2}
    {α : ∀ s, J.obj s ⟶ J'.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction K).map (transformComponent hα M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J' K).hom.app M ≫ transformComponent (hα.whiskerRight K) M := by
  apply rectangular_square_of_total
  intro w
  rw [rectangular_induction_map_total K (transformComponent_mem hα M), rectangular_transform_total]
  have h := compForward_transform_inner K hα M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

/-- The independent outer transformation maps to its source whisker after flattening. -/
theorem inductionComp_outer_transform
    (K' : A ⥤ B) [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
    {p : ZMod 2} {β : ∀ s, K.obj s ⟶ K'.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hβ ((induction J).obj M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K').hom.app M ≫ transformComponent (hβ.whiskerLeft J) M := by
  apply rectangular_square_of_total
  intro w
  rw [rectangular_transform_total, rectangular_transform_total]
  have h := compForward_transform_outer J hβ M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

end OddMath.QuiverHecke.ELVOld.BalancedInduction

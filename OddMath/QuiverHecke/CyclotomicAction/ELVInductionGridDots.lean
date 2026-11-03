import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierPowers

/-! # Dots under the induction-composition comparison

Brundan–Ellis (1.7)–(1.8): the chosen composition comparison transports
inner and outer module dots to the corresponding whiskered source arrows.
These module equations retain the given induced objects and ordinary maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]

private theorem module_square_of_total
    {M N : Superfunctor k B (SVec k)} (a : End M) (e : M ⟶ N) (b : End N)
    (h : ∀ w, SVec.toLinearMap (e.total w) ∘ₗ SVec.toLinearMap (a.total w) =
      SVec.toLinearMap (b.total w) ∘ₗ SVec.toLinearMap (e.total w)) :
    a ≫ e = e ≫ b := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  exact LinearMap.congr_fun (h w) x

private theorem induction_map_total
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

private theorem dot_total
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k)) (w : A) :
    (dotEnd J hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [dotEnd, SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2}

/-- Flattening intertwines induction of the inner dot with its source whisker. -/
theorem inductionComp_inner_dot
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction K).map (dotEnd J hα M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K).hom.app M ≫ dotEnd (J ⋙ K) (hα.whiskerRight K) M := by
  apply module_square_of_total
  intro w
  rw [induction_map_total K (dotEnd_mem J hα M), dot_total]
  have h := compForward_transform_inner K hα M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, dotEnd, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

/-- Flattening intertwines the outer dot with its source whisker. -/
theorem inductionComp_outer_dot
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    dotEnd K hβ ((induction J).obj M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K).hom.app M ≫ dotEnd (J ⋙ K) (hβ.whiskerLeft J) M := by
  apply module_square_of_total
  intro w
  rw [dot_total, dot_total]
  have h := compForward_transform_outer J hβ M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

end OddMath.QuiverHecke.ELVOld.BalancedInduction

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Two-functor induction crossing tensors

Canonical induction composition transports a homogeneous crossing between
two append functors. This is the generator comparison needed to evaluate
the distinct-colour cup-crossing-cap in Brundan–Ellis (1.12).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def mixedFlatten (M : Superfunctor k C (SVec k)) :
    induced B (induced A M) ⟶ induced (A ⋙ B) M := (inductionComp A B).hom.app M

private def mixedUnflatten (M : Superfunctor k C (SVec k)) :
    induced (A ⋙ B) M ⟶ induced B (induced A M) := (inductionComp A B).inv.app M

private theorem mixedFlatten_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : B.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (mixedFlatten A B M).total t
      (tensor B (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor (A ⋙ B) M.toFunctor s (B.map h ≫ g) b :=
  inductionComp_hom_total_tensor A B M s w t g h b

private theorem mixedUnflatten_tensor (M : Superfunctor k C (SVec k))
    (s t : C) (g : (A ⋙ B).obj s ⟶ t) (b : M.obj s) :
    (mixedUnflatten A B M).total t (tensor (A ⋙ B) M.toFunctor s g b) =
    tensor B (induced A M).toFunctor (A.obj s) g (tensor A M.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor A B M s t g b

/-- Canonical pair contraction, the signed crossing, and canonical expansion. -/
def mixedCrossComponent (M : Superfunctor k C (SVec k)) :
    induced B (induced A M) ⟶ induced A (induced B M) :=
  mixedFlatten A B M ≫ transformComponent hα M ≫ mixedUnflatten B A M

theorem mixedCrossComponent_supernatural :
    IsSupernatural k p (F := induction A ⋙ induction B) (G := induction B ⋙ induction A)
      (mixedCrossComponent A B hα) := by
  have hL := isSupernatural_of_natTrans (inductionComp (k := k) A B).hom
    (fun M => inductionComp_hom_mem A B M)
  have hT := transformComponent_supernatural hα
  have hR := isSupernatural_of_natTrans (inductionComp (k := k) B A).inv
    (fun M => inductionComp_inv_mem B A M)
  change IsSupernatural k p (F := induction A ⋙ induction B)
    (G := induction B ⋙ induction A) (fun M =>
      (inductionComp (k := k) A B).hom.app M ≫
        transformComponent hα M ≫ (inductionComp (k := k) B A).inv.app M)
  simpa only [zero_add, add_zero, Category.assoc] using hL.comp (hT.comp hR)

private theorem mixed_transform_total (M : Superfunctor k C (SVec k)) (w : C) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with h | h
  · simp only [SuperNatTrans.total, transformComponent_app, h, ↓reduceIte,
      one_ne_zero, add_zero]
  · simp only [SuperNatTrans.total, transformComponent_app, h, ↓reduceIte,
      zero_ne_one, zero_add]

private theorem mixedCrossComponent_total (M : Superfunctor k C (SVec k))
    (t : C) (x : Obj B (induced A M).toFunctor t) :
    (mixedCrossComponent A B hα M).total t x =
      (mixedUnflatten B A M).total t
        ((transformComponent hα M).total t ((mixedFlatten A B M).total t x)) := by
  rw [mixedCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

theorem mixedCrossComponent_total_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : B.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (mixedCrossComponent A B hα M).total t
      (tensor B (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor A (induced B M).toFunctor (B.obj s)
      (α s ≫ twist k p (B.map h ≫ g))
      (tensor B M.toFunctor s (𝟙 _) b) := by
  rw [mixedCrossComponent_total, mixedFlatten_tensor]
  have ht := congrArg
    (fun f : Obj (A ⋙ B) M.toFunctor t →ₗ[k] Obj (B ⋙ A) M.toFunctor t =>
      f (tensor (A ⋙ B) M.toFunctor s (B.map h ≫ g) b)) (mixed_transform_total A B hα M t)
  have he := transformLinear_tensor hα M t s (B.map h ≫ g) b
  have hx := congrArg (fun x : Obj (B ⋙ A) M.toFunctor t =>
    (mixedUnflatten B A M).total t x) (ht.trans he)
  exact hx.trans (mixedUnflatten_tensor B A M s t
    (α s ≫ twist k p (B.map h ≫ g)) b)

end OddMath.QuiverHecke.ELVOld.BalancedInduction

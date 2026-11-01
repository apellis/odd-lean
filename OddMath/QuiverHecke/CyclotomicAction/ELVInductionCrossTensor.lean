import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Generator formula for a canonically transported induction transformation

The existing induction-composition isomorphism conjugates a homogeneous
transformation of a double functor. Its action on nested balanced tensors
retains the ordered composite and the full parity twist. The comparison
is exactly the existing canonical `inductionComp`, in both directions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
variable {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

private theorem transform_total (M : Superfunctor k C (SVec k))
    (w : C) :
    (BalancedInduction.transformComponent (hα) M).total w =
      BalancedInduction.transformLinear (hα) M w := by
  rcases parity_eq_zero_or_one p with h | h
  · simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app, h,
      ↓reduceIte, one_ne_zero, add_zero]
  · simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app, h,
      ↓reduceIte, zero_ne_one, zero_add]

private def flatten (M : Superfunctor k C (SVec k)) :
    BalancedInduction.induced A
      (BalancedInduction.induced A M) ⟶
    BalancedInduction.induced (A ⋙ A) M :=
  (BalancedInduction.inductionComp (k := k) A
    A).hom.app M

private def unflatten (M : Superfunctor k C (SVec k)) :
    BalancedInduction.induced (A ⋙ A) M ⟶
    BalancedInduction.induced A
      (BalancedInduction.induced A M) :=
  (BalancedInduction.inductionComp (k := k) A
    A).inv.app M

private theorem flatten_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : A.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (flatten A M).total t
      (tensor A (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor (A ⋙ A) M.toFunctor s (A.map h ≫ g) b :=
  inductionComp_hom_total_tensor A A M s w t g h b

private theorem unflatten_tensor (M : Superfunctor k C (SVec k))
    (s t : C) (g : (A ⋙ A).obj s ⟶ t) (b : M.obj s) :
    (unflatten A M).total t (tensor (A ⋙ A) M.toFunctor s g b) =
    tensor A (induced A M).toFunctor (A.obj s) g (tensor A M.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor A A M s t g b

def doubleCrossComponent (M : Superfunctor k C (SVec k)) :
    End (BalancedInduction.induced A
      (BalancedInduction.induced A M)) :=
  flatten A M ≫
    BalancedInduction.transformComponent (hα) M ≫
      unflatten A M

private theorem doubleCrossComponent_total (M : Superfunctor k C (SVec k))
    (t : C) (x : Obj A (induced A M).toFunctor t) :
    (doubleCrossComponent A hα M).total t x =
      (unflatten A M).total t
        ((transformComponent hα M).total t ((flatten A M).total t x)) := by
  rw [doubleCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

theorem doubleCrossComponent_total_tensor (M : Superfunctor k C (SVec k))
    (s w t : C)
    (g : A.obj w ⟶ t)
    (h : A.obj s ⟶ w) (b : M.obj s) :
    (doubleCrossComponent A hα M).total t
      (BalancedInduction.tensor A
        (BalancedInduction.induced A M).toFunctor w g
          (BalancedInduction.tensor A M.toFunctor s h b)) =
    BalancedInduction.tensor A
      (BalancedInduction.induced A M).toFunctor
      (A.obj s)
      (α s ≫
        twist k p (A.map h ≫ g))
      (BalancedInduction.tensor A M.toFunctor s (𝟙 _) b) := by
  rw [doubleCrossComponent_total, flatten_tensor]
  have ht := congrArg
    (fun f : Obj (A ⋙ A) M.toFunctor t →ₗ[k] Obj (A ⋙ A) M.toFunctor t =>
      f (tensor (A ⋙ A) M.toFunctor s (A.map h ≫ g) b)) (transform_total A hα M t)
  have he := transformLinear_tensor hα M t s (A.map h ≫ g) b
  have hx := congrArg (fun x : Obj (A ⋙ A) M.toFunctor t =>
    (unflatten A M).total t x) (ht.trans he)
  exact hx.trans (unflatten_tensor A M s t (α s ≫ twist k p (A.map h ≫ g)) b)

end OddMath.QuiverHecke.ELVOld.BalancedInduction

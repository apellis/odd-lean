import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossTensor

/-! # Tensor evaluation of the ordered induction mate

The cup, canonically transported signed double transformation and cap are
composed in that order. The generator formula keeps the whole parity twist.
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

private def moduleUnit (M : Superfunctor k C (SVec k)) :
    M ⟶ (restriction A).obj (induced A M) := (adjunctionUnit A).app M

private def moduleCounit (N : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj N) ⟶ N := (adjunctionCounit A).app N

private def inducedCounit (N : Superfunctor k C (SVec k)) :
    induced A (induced A ((restriction A).obj N)) ⟶ induced A N :=
  (induction A).map (moduleCounit A N)

private theorem unit_total_apply (M : Superfunctor k C (SVec k)) (t : C) (b : M.obj t) :
    (moduleUnit A M).total t b = unit A M.toFunctor t b := by
  simp only [moduleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem counit_total_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (A.obj s)) :
    (moduleCounit A N).total t
      (tensor A ((restriction A).obj N).toFunctor s g b) = N.map g b := by
  simp only [moduleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor A N.toFunctor t s g b

private theorem restriction_map_total_apply
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (t : C) (b : M.obj (A.obj t)) :
    ((restriction A).map f).total t b = f.total (A.obj t) b := rfl

private theorem neg_total_apply
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (t : C) (x : P.obj t) :
    (-f).total t x = -(f.total t x) := by
  change -(f.app 0 t x) + -(f.app 1 t x) = -(f.app 0 t x + f.app 1 t x)
  exact (neg_add _ _).symm

private theorem induction_map_even_tensor
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0)
    (s t : C) (g : A.obj s ⟶ t) (b : M.obj s) :
    ((induction A).map f).total t (tensor A M.toFunctor s g b) =
    tensor A N.toFunctor s g (f.total s b) := by
  have h1 := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap A f).total t _ = _
  rw [moduleMap_total_tensor, h1]
  simp only [SuperNatTrans.total, h1, add_zero]
  change tensor A N.toFunctor s g (f.app 0 s b) +
    tensor A N.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

def orderedMateComponent (N : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj N) ⟶ (restriction A).obj (induced A N) :=
  moduleUnit A (induced A ((restriction A).obj N)) ≫
    (restriction A).map (-doubleCrossComponent A hα ((restriction A).obj N)) ≫
    (restriction A).map (inducedCounit A N)

private theorem orderedMateComponent_total (N : Superfunctor k C (SVec k))
    (t : C) (x : (induced A ((restriction A).obj N)).obj t) :
    (orderedMateComponent A hα N).total t x =
      ((inducedCounit A N).total (A.obj t))
        ((-doubleCrossComponent A hα ((restriction A).obj N)).total (A.obj t)
          (unit A (induced A ((restriction A).obj N)).toFunctor t x)) := by
  rw [orderedMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [unit_total_apply, restriction_map_total_apply, restriction_map_total_apply]

theorem orderedMateComponent_total_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (A.obj s)) :
    (orderedMateComponent A hα N).total t
      (tensor A ((restriction A).obj N).toFunctor s g b) =
    -tensor A N.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b := by
  rw [orderedMateComponent_total, unit_apply, neg_total_apply,
    doubleCrossComponent_total_tensor]
  rw [map_neg]
  have he := induction_map_even_tensor A
    (M := induced A ((restriction A).obj N)) (N := N)
    (moduleCounit A N) (adjunctionCounit_mem A N)
    (A.obj s) (A.obj t) (α s ≫ twist k p (A.map g ≫ 𝟙 _))
    (tensor A ((restriction A).obj N).toFunctor s (𝟙 _) b)
  have hc := counit_total_tensor A N s (A.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (A.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (A.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (A.obj s) =>
    tensor A N.toFunctor (A.obj s) (α s ≫ twist k p (A.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := congrArg Neg.neg (he.trans hr)
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELVOld.BalancedInduction

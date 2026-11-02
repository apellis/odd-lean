import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMixedCrossTensor

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
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def moduleUnit (M : Superfunctor k C (SVec k)) :
    M ⟶ (restriction A).obj (induced A M) := (adjunctionUnit A).app M

private def moduleCounit (N : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj N) ⟶ N := (adjunctionCounit A).app N

private def inducedCounit (N : Superfunctor k C (SVec k)) :
    induced A (induced B ((restriction B).obj N)) ⟶ induced A N :=
  (induction A).map (moduleCounit B N)

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

def orderedMixedMateComponent (N : Superfunctor k C (SVec k)) :
    induced A ((restriction B).obj N) ⟶ (restriction B).obj (induced A N) :=
  moduleUnit B (induced A ((restriction B).obj N)) ≫
    (restriction B).map (mixedCrossComponent A B hα ((restriction B).obj N)) ≫
    (restriction B).map (inducedCounit A B N)

private theorem orderedMixedMateComponent_total (N : Superfunctor k C (SVec k))
    (t : C) (x : (induced A ((restriction B).obj N)).obj t) :
    (orderedMixedMateComponent A B hα N).total t x =
      ((inducedCounit A B N).total (B.obj t))
        ((mixedCrossComponent A B hα ((restriction B).obj N)).total (B.obj t)
          (unit B (induced A ((restriction B).obj N)).toFunctor t x)) := by
  rw [orderedMixedMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [unit_total_apply, restriction_map_total_apply, restriction_map_total_apply]

theorem orderedMixedMateComponent_total_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    (orderedMixedMateComponent A B hα N).total t
      (tensor A ((restriction B).obj N).toFunctor s g b) =
    tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g)) b := by
  rw [orderedMixedMateComponent_total, unit_apply, mixedCrossComponent_total_tensor]
  have he := induction_map_even_tensor A
    (M := induced B ((restriction B).obj N)) (N := N)
    (moduleCounit B N) (adjunctionCounit_mem B N)
    (B.obj s) (B.obj t) (α s ≫ twist k p (B.map g ≫ 𝟙 _))
    (tensor B ((restriction B).obj N).toFunctor s (𝟙 _) b)
  have hc := counit_total_tensor B N s (B.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (B.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (B.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (B.obj s) =>
    tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := he.trans hr
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELVOld.BalancedInduction

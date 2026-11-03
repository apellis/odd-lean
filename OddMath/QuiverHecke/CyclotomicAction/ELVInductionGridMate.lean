import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform

/-! # The ordered crossing mate between changing content categories

The first crossing-derived entry of DeformedMatrixComparison (2), (4)
uses the unit for the upper append adjunction, the prescribed signed
crossing, and induction of the lower append counit. Keeping the three
categories distinct gives the mate needed by the scalar and fixed-content
matrix charts in DeformedActionAssembly §§5–6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The given homogeneous crossing conjugated by both chosen flattenings. -/
def gridDoubleCrossComponent (M : Superfunctor k C (SVec k)) :
    (induction J ⋙ induction K).obj M ⟶ (induction J ⋙ induction K).obj M :=
  (inductionComp J K).hom.app M ≫ transformComponent hα M ≫
    (inductionComp J K).inv.app M

private theorem gridDoubleCrossComponent_total_tensor
    (M : Superfunctor k C (SVec k)) (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    (((inductionComp J K).hom.app M ≫ transformComponent hα M ≫
      (inductionComp J K).inv.app M).total w)
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) :=
  (doubleTransformLinear_eq_total J K hα M w
    (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b))).symm.trans
      (doubleTransformLinear_tensor J K hα M s v w a g b)

private def gridModuleUnit (M : Superfunctor k A (SVec k)) :
    M ⟶ (restriction K).obj (induced K M) := (adjunctionUnit K).app M

private def gridModuleCounit (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ N := (adjunctionCounit J).app N

private def gridInducedCounit (N : Superfunctor k A (SVec k)) :
    induced K (induced J ((restriction J).obj N)) ⟶ induced K N :=
  (induction K).map (gridModuleCounit J N)

private theorem gridUnit_total_apply (M : Superfunctor k A (SVec k)) (t : A) (b : M.obj t) :
    (gridModuleUnit K M).total t b = unit K M.toFunctor t b := by
  simp only [gridModuleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem gridCounit_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (gridModuleCounit J N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) = N.map g b := by
  simp only [gridModuleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor J N.toFunctor t s g b

private theorem gridRestriction_total_apply
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : A) (b : M.obj (K.obj t)) :
    ((restriction K).map f).total t b = f.total (K.obj t) b := rfl

private theorem gridNeg_total_apply
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : B) (b : M.obj t) :
    (-f).total t b = -(f.total t b) := by
  change -(f.app 0 t b) + -(f.app 1 t b) = -(f.app 0 t b + f.app 1 t b)
  exact (neg_add _ _).symm

private theorem gridInduction_map_even_tensor
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0)
    (s : A) (t : B) (g : K.obj s ⟶ t) (b : M.obj s) :
    ((induction K).map f).total t (tensor K M.toFunctor s g b) =
      tensor K N.toFunctor s g (f.total s b) := by
  have h1 := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap K f).total t _ = _
  rw [moduleMap_total_tensor, h1]
  simp only [SuperNatTrans.total, h1, add_zero]
  change tensor K N.toFunctor s g (f.app 0 s b) +
    tensor K N.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

/-- The ordinary-adjunction mate, with the upper append unit, prescribed
signed crossing, and induced lower append counit in their given order. -/
def orderedGridMateComponent (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ (restriction K).obj (induced K N) :=
  gridModuleUnit K (induced J ((restriction J).obj N)) ≫
    (restriction K).map (-gridDoubleCrossComponent J K hα ((restriction J).obj N)) ≫
    (restriction K).map (gridInducedCounit J K N)

private theorem orderedGridMateComponent_total (N : Superfunctor k A (SVec k))
    (t : A) (x : (induced J ((restriction J).obj N)).obj t) :
    (orderedGridMateComponent J K hα N).total t x =
      (gridInducedCounit J K N).total (K.obj t)
        ((-gridDoubleCrossComponent J K hα ((restriction J).obj N)).total (K.obj t)
          (unit K (induced J ((restriction J).obj N)).toFunctor t x)) := by
  rw [orderedGridMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [gridUnit_total_apply, gridRestriction_total_apply, gridRestriction_total_apply]
  rfl

/-- The mate retains the extra minus and twists the complete appended
coefficient arrow. No homogeneity condition is imposed on that arrow. -/
theorem orderedGridMateComponent_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (orderedGridMateComponent J K hα N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) =
      -tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g)) b := by
  rw [orderedGridMateComponent_total, unit_apply, gridNeg_total_apply]
  unfold gridDoubleCrossComponent
  rw [gridDoubleCrossComponent_total_tensor, map_neg]
  have he := gridInduction_map_even_tensor K
    (M := induced J ((restriction J).obj N)) (N := N)
    (gridModuleCounit J N) (adjunctionCounit_mem J N)
    (J.obj s) (K.obj t) (α s ≫ twist k p (K.map g ≫ 𝟙 _))
    (tensor J ((restriction J).obj N).toFunctor s (𝟙 _) b)
  have hc := gridCounit_total_tensor J N s (J.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (J.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (J.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (J.obj s) =>
    tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := congrArg Neg.neg (he.trans hr)
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELVOld.BalancedInduction

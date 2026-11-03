import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso

/-! # Input-module supernaturality of the signed grid mate

DeformedMatrixComparison (4), (5) needs the prescribed same-colour grid
mate on all input module maps. Its crossing has the extra minus, whereas
the rectangular mate of Brundan--Ellis (1.12) uses the positive crossing.
The negative crossing is retained while composing the homogeneous family laws.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem gridFamily_neg
    {k : Type u} {C A : Type*} [CommRing k] [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} {p : ZMod 2} {α : ∀ N, F.obj N ⟶ G.obj N}
    (hα : IsSupernatural k p α) : IsSupernatural k p (fun N => -α N) where
  mem N := (parity (R := k) _ _ p).neg_mem (hα.mem N)
  naturality hf := by
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp, smul_neg] using
      congrArg Neg.neg (hα.naturality hf)

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The given chosen flatten-crossing-unflatten family is supernatural
in every input-module map. -/
theorem gridDoubleCrossComponent_supernatural :
    IsSupernatural k p (F := induction J ⋙ induction K) (G := induction J ⋙ induction K)
      (gridDoubleCrossComponent J K hα) := by
  have h₁ := isSupernatural_of_natTrans (inductionComp (k := k) J K).hom
    (fun N => inductionComp_hom_mem J K N)
  have h₂ := transformComponent_supernatural hα
  have h₃ := isSupernatural_of_natTrans (inductionComp (k := k) J K).inv
    (fun N => inductionComp_inv_mem J K N)
  change IsSupernatural k p (F := induction J ⋙ induction K) (G := induction J ⋙ induction K)
    (fun N => (inductionComp J K).hom.app N ≫ transformComponent hα N ≫
      (inductionComp J K).inv.app N)
  simpa only [zero_add, add_zero, Category.assoc] using h₁.comp (h₂.comp h₃)

/-- The prescribed signed mate is supernatural in arbitrary input-module
maps; no map is restricted to even parity. The extra crossing minus remains
inside the actual component. -/
theorem orderedGridMateComponent_supernatural :
    IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) J)
      (G := induction (k := k) K ⋙ restriction (k := k) K)
      (orderedGridMateComponent J K hα) := by
  have hU₀ := isSupernatural_of_natTrans (R := k) (adjunctionUnit (k := k) K)
    (fun N => adjunctionUnit_mem (k := k) K N)
  have hU := hU₀.whiskerLeft (restriction (k := k) J ⋙ induction (k := k) J)
  have hX₀ := gridFamily_neg (gridDoubleCrossComponent_supernatural J K hα)
  have hX := (hX₀.whiskerLeft (restriction (k := k) J)).whiskerRight (restriction (k := k) K)
  have hC₀ := isSupernatural_of_natTrans (R := k) (adjunctionCounit (k := k) J)
    (fun N => adjunctionCounit_mem (k := k) J N)
  have hC := (hC₀.whiskerRight (induction (k := k) K)).whiskerRight (restriction (k := k) K)
  change IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) J)
    (G := induction (k := k) K ⋙ restriction (k := k) K)
    (fun N => (adjunctionUnit K).app (induced J ((restriction J).obj N)) ≫
      (restriction K).map (-gridDoubleCrossComponent J K hα ((restriction J).obj N)) ≫
      (restriction K).map ((induction K).map ((adjunctionCounit J).app N)))
  have h := hU.comp (hX.comp hC)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at h ⊢
  simpa only [Functor.comp_id, Functor.id_comp, Functor.comp_obj, zero_add, add_zero,
    Category.assoc] using h
end OddMath.QuiverHecke.ELVOld.BalancedInduction

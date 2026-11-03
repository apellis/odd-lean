import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleRelations

/-! # The square of the induction-grid crossing

Brundan–Ellis (1.7): a square-zero source crossing induces the square-zero
chosen negative crossing on the double induction, on every input module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)

/-- The physical double crossing is square-zero under the chosen flattening. -/
theorem gridDoubleCrossComponent_square (hs : ∀ s, γ s ≫ γ s = 0)
    (M : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent J K hγ M ≫ gridDoubleCrossComponent J K hγ M = 0 := by
  have hlinear : ∀ w, (transformLinear hγ M w).comp (transformLinear hγ M w) = 0 := by
    intro w
    rw [transformLinear_comp]
    have hz : transformLinear (hγ.comp hγ) M w = 0 := by
      apply hom_ext
      intro s g b
      rw [transformLinear_tensor]
      change tensor (J ⋙ K) M.toFunctor s ((γ s ≫ γ s) ≫ _) b = 0
      rw [hs s, Limits.zero_comp]
      simp only [tensor, TensorProduct.zero_tmul, map_zero]
    rw [hz, smul_zero]
  have hm := transformComponent_square_of_linear hγ M hlinear
  dsimp only [gridDoubleCrossComponent]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (transformComponent hγ M), hm, Limits.zero_comp, Limits.comp_zero]

/-- Evaluation retains the selected negative module crossing. -/
theorem inductionModuleCross_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleCross J K hγ).total M = -gridDoubleCrossComponent J K hγ M := by
  change -((gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans.app 0 M) +
      -((gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans.app 1 M) = _
  rw [← neg_add]
  exact congrArg Neg.neg (OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K)
    (G := inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K)
    (gridDoubleCrossComponent_supernatural J K hγ) M)

/-- The specified negative Rouquier crossing, as a two-morphism, is square-zero. -/
theorem inductionModuleCross_square (hs : ∀ s, γ s ≫ γ s = 0) :
    inductionModuleCross J K hγ ≫ inductionModuleCross J K hγ = 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, inductionModuleCross_total]
  change (-gridDoubleCrossComponent J K hγ M) ≫ (-gridDoubleCrossComponent J K hγ M) = 0
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using
    gridDoubleCrossComponent_square J K hγ hs M

end OddMath.QuiverHecke.ELVOld.BalancedInduction

import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierInverse

/-! # The induction-grid local Rouquier record

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): source nilHecke relations and
specified even matrix inverses assemble the local record with its ordinary
adjunctions, unchanged dots, and negative physical crossing. The matrix
inputs here are intermediate; old-content applications supply them from
the constructed prescribed inverses.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem cup_as_function
    {k : Type u} [CommRing k] {R S : PiSCat.{u,u,u+1} k}
    {E : R ⟶ S} {F : S ⟶ R} (A : SKM.SuperAdjunction (k := k) E F) (x : End E) :
    SKM.RouquierBoundary.cup A x = (fun n => A.unit ≫ SKM.rouquierPower x n ▷ F) := rfl

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2}
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

/-- The local record for the specified induction fields. The matrix
isomorphisms are intermediate inputs, removed by the old-content constructor. -/
def inductionModuleLoc (c : ℤ)
    (hleft : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (K.map (α s) ≫ γ s) (sign k (p*p) • (γ s ≫ β (J.obj s))) = 𝟙 _)
    (hright : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (γ s ≫ K.map (α s)) (sign k (p*p) • (β (J.obj s) ≫ γ s)) = 𝟙 _)
    (eU : ∀ (_ : 0 ≤ c) N, OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N c.toNat) ≅
      (restriction K).obj (induced K N))
    (heU : ∀ hc N, (eU hc N).hom = gridUnitMatrixModuleMap J K hγ hβ N c.toNat)
    (eC : ∀ (_ : c ≤ 0) N, induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N (-c).toNat))
    (heC : ∀ hc N, (eC hc N).hom = gridCapMatrixModuleMap J K hγ hα N (-c).toNat) :
    SKM.SuperRouquierLoc (k := k)
      (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
      (inductionModuleDot J hα) (inductionModuleDot K hβ) (inductionModuleCross J K hγ) p (-c) where
  dot₁_mem := inductionModuleDot_mem J hα
  dot₂_mem := inductionModuleDot_mem K hβ
  cross_mem := inductionModuleCross_mem J K hγ
  slide_left := inductionModuleCross_slide_left J K hγ hα hβ hleft
  slide_right := inductionModuleCross_slide_right J K hγ hα hβ hright
  invPos hh := inductionModuleInverseToFamily J K hγ hα (-c).toNat
    (eC (by omega)) (heC (by omega))
  invNeg hh := by
    have H := inductionModuleInverseFromFamily J K hγ hβ c.toNat
      (eU (by omega)) (heU (by omega))
    rw [cup_as_function] at H
    simpa only [neg_neg] using H

end OddMath.QuiverHecke.ELVOld.BalancedInduction

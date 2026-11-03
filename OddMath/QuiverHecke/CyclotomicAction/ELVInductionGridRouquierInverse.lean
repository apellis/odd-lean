import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierPowers
import OddMath.SKM.AugmentedInverseProfile

/-! # The grid inverse entries for the prescribed Rouquier fields

Brundan–Ellis (1.13)–(1.14): the constructed grid inverse families have
the actual negative-crossing Rouquier mate, ordinary right-unit/dot and
right-counit/dot fields. Their finite profile is the local presentation's
`(n : ZMod 2) * p`, with every inverse entry retained literally.
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
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
  (m : ℕ)

/-- The specified unit matrix supplies all local inverse fields for the
actual Rouquier mate and dotted units. Matrix isomorphisms are intermediate
inputs, supplied by constructed old-content inverses in applications. -/
def inductionModuleInverseFromFamily
    (e : ∀ N, OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N))
    (he : ∀ N, (e N).hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    SKM.SuperSumInvFrom (k := k)
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
        (inductionModuleCross J K hγ))
      (SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hβ))
      p (fun n => (n : ZMod 2) * p) m := by
  rw [inductionModuleMate_eq_grid]
  have hu : SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hβ) =
      gridUnitColumnTransformation K hβ := funext (inductionModuleUnitPower_eq K hβ)
  rw [hu]
  exact (gridLocalInverseFromFamily J K hγ hβ m e he).mulProfile

/-- The specified cap matrix supplies the local inverse fields for the
same Rouquier mate and ordinary dotted right counits. -/
def inductionModuleInverseToFamily
    (e : ∀ N, induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m))
    (he : ∀ N, (e N).hom = gridCapMatrixModuleMap J K hγ hα N m) :
    SKM.SuperSumInvTo (k := k)
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
        (inductionModuleCross J K hγ))
      (fun n => restrictionModuleCell (k := k) J ◁ SKM.rouquierPower (inductionModuleDot J hα) n ≫
        (inductionModuleAdjunction (k := k) J).counit)
      p (fun n => (n : ZMod 2) * p) m := by
  rw [inductionModuleMate_eq_grid]
  have hc : (fun n => restrictionModuleCell (k := k) J ◁ SKM.rouquierPower (inductionModuleDot J hα) n ≫
      (inductionModuleAdjunction (k := k) J).counit) = gridCapRowTransformation J hα :=
    funext (inductionModuleCapPower_eq J hα)
  rw [hc]
  exact (gridLocalInverseToFamily J K hγ hα m e he).mulProfile

end OddMath.QuiverHecke.ELVOld.BalancedInduction

import OddMath.QuiverHecke.CyclotomicAction.ELVGridLocalInverseFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRouquierMate

/-! # The induction-grid fields in the Rouquier target

Brundan–Ellis (1.13)–(1.14): retain the ordinary induction adjunction,
the chosen dot, and the negative equal-colour double crossing when
attaching the prescribed grid inverse entries to the local data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]

/-- The canonical parity category of modules on a supercategory. -/
def inductionModulePiCategory (C : Type u) [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C] : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k C (SVec k))
  pi := supermodulePiSupercategory

variable {C A B : Type u}
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- Balanced induction as a cell in the chosen parity target. -/
def inductionModuleCell : inductionModulePiCategory (k := k) C ⟶ inductionModulePiCategory (k := k) A :=
  show Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k A (SVec k)) from
    ⟨induction (k := k) J⟩
/-- Restriction as a cell in the same parity target. -/
def restrictionModuleCell : inductionModulePiCategory (k := k) A ⟶ inductionModulePiCategory (k := k) C :=
  show Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k)) from
    ⟨restriction (k := k) J⟩
/-- The existing even ordinary adjunction on these exact cells. -/
def inductionModuleAdjunction :
    SKM.SuperAdjunction (k := k) (inductionModuleCell (k := k) J) (restrictionModuleCell (k := k) J) :=
  ordinaryEvenSuperAdjunction (inductionModuleCell (k := k) J) (restrictionModuleCell (k := k) J)
    (adjunction J) (adjunctionUnit_mem J) (adjunctionCounit_mem J)

variable {p : ZMod 2}
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)

/-- The specified induced dot, without any new sign convention. -/
def inductionModuleDot : End (inductionModuleCell (k := k) J) :=
  (transformComponent_supernatural hα).toSuperNatTrans
/-- The Rouquier crossing uses the negative of the physical grid crossing. -/
def inductionModuleCross : End (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K) :=
  -(show End (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K) from
    (gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans)

theorem inductionModuleDot_mem :
    inductionModuleDot J hα ∈ parity (R := k) _ _ p :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem (transformComponent_supernatural hα)
theorem inductionModuleCross_mem :
    inductionModuleCross J K hγ ∈ parity (R := k) _ _ p :=
  (parity (R := k) _ _ p).neg_mem
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem (gridDoubleCrossComponent_supernatural J K hγ))

/-- Its ordered Rouquier mate is the exact prescribed grid principal field. -/
theorem inductionModuleMate_eq_grid :
    SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
      (inductionModuleCross J K hγ) = gridMateTransformation J K hγ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [OddMath.HomogeneousSuperfunctorIso.total_eq_app _
    (SKM.rouquierMate_homogeneous (inductionModuleAdjunction (k := k) J)
      (inductionModuleAdjunction (k := k) K) (inductionModuleCross_mem J K hγ)) N]
  rw [SKM.rouquierMate_piscat_app, gridMateTransformation_total]
  simp only [inductionModuleCross, Superfunctor.neg_app, IsSupernatural.toSuperNatTrans,
    ↓reduceIte]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

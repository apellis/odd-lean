import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields
import OddMath.SKM.RouquierBoundary

/-! # The prescribed dotted fields in the induction-grid Rouquier target

Brundan–Ellis (1.13)–(1.14): ordered powers of the given dot followed or
preceded by the ordinary right-adjunction maps are exactly the specified
unit columns and cap rows on all input modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u+1} k}
    {F : A ⟶ B} (d : End F) (n : ℕ) (M : A) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]
private theorem whiskerRight_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm
private theorem whiskerLeft_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (H : A ⟶ B) {F G : B ⟶ R} (η : F ⟶ G) (M : A) :
    (H ◁ η).total M = η.total (H.obj M) := rfl

variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- Evaluation retains the given module induction dot. -/
theorem inductionModuleDot_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleDot J hα).total M = dotEnd J hα M :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := inductionModuleCell (k := k) J) (G := inductionModuleCell (k := k) J)
    (transformComponent_supernatural hα) M
private theorem module_unit_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleAdjunction (k := k) J).unit.total M = (adjunctionUnit J).app M := by
  change (adjunctionUnit J).app M + 0 = _
  exact add_zero _
private theorem module_counit_total (N : Superfunctor k A (SVec k)) :
    (inductionModuleAdjunction (k := k) J).counit.total N = (adjunctionCounit J).app N := by
  change (adjunctionCounit J).app N + 0 = _
  exact add_zero _

/-- The given Rouquier dotted unit is precisely the ordinary module column. -/
theorem inductionModuleUnitPower_eq (n : ℕ) :
    SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J) (inductionModuleDot J hα) n =
      gridUnitColumnTransformation J hα n := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  unfold SKM.RouquierBoundary.cup
  rw [Superfunctor.comp_total, whiskerRight_total, power_total, inductionModuleDot_total,
    module_unit_total, gridUnitColumnTransformation_total]
  rfl

/-- The given Rouquier dotted counit is precisely the ordinary module row. -/
theorem inductionModuleCapPower_eq (n : ℕ) :
    restrictionModuleCell (k := k) J ◁ SKM.rouquierPower (inductionModuleDot J hα) n ≫
      (inductionModuleAdjunction (k := k) J).counit = gridCapRowTransformation J hα n := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, whiskerLeft_total, power_total, inductionModuleDot_total,
    module_counit_total, gridCapRowTransformation_total]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

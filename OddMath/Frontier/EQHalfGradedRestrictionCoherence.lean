import OddMath.Frontier.EQHalfGradedUnitParityCoherence

/-!
# Localization computations for actual restriction comparisons

The existing derived restriction-composition isomorphism computes on localized
modules to the original module composition comparison. We first expose its
homotopy-localization origin, then compute the quotient comparison structurally.
The existing module-localization restriction comparison also respects coherent
integer shifts. Source, intermediate, and target derived Hom universes are independent.

These are prerequisites for comparing `restrictParityIso` with the localized module
parity comparison. That parity comparison and its derived involution coherence are
not proved here. No replacement functor, shift structure, or involution is introduced.
-/

noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe w₁ w₂ w₃ w v₁ v₂ v₃ u₁ u₂ u₃
namespace OddMath.Frontier.RestrictionCoherence
open DG.CatModule
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [∀ X Y : C, DG.DGAddCommGroup (X ⟶ Y)] [DG.DGCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DG.DGAddCommGroup (X ⟶ Y)] [DG.DGCategory D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [∀ X Y : E, DG.DGAddCommGroup (X ⟶ Y)] [DG.DGCategory E]
  [HasDerivedCategory.{w₁, w} C] [HasDerivedCategory.{w₂, w} D]
  [HasDerivedCategory.{w₃, w} E]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]
  (G : D ⥤ E) [G.Additive] [G.IsDGFunctor]

open DerivedCategory in
/-- The existing derived comparison restricts to the actual homotopy comparison. -/
theorem Qh_restrictCompIso_natIso :
    Functor.isoWhiskerLeft Qh (restrictCompIso F G) =
      QhCompRestrictIso (F ⋙ G) ≪≫
        Functor.isoWhiskerRight (HomotopyCategory.precompCompIso F G) Qh ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (QhCompRestrictIso F).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (QhCompRestrictIso G).symm _ ≪≫
        Functor.associator _ _ _ := by
  apply Iso.ext
  exact ((Functor.whiskeringLeft _ _ _).obj Qh).map_preimage _

open DerivedCategory in
/-- Component formula with no transported or replacement comparison. -/
theorem Qh_restrictCompIso_hom_app (M : HomotopyCategory.{w} E) :
    (restrictCompIso F G).hom.app (Qh.obj M) =
      (QhCompRestrictIso (F ⋙ G)).hom.app M ≫
        Qh.map ((HomotopyCategory.precompCompIso F G).hom.app M) ≫
        (QhCompRestrictIso F).inv.app ((HomotopyCategory.precomp G).obj M) ≫
        (restrict F).map ((QhCompRestrictIso G).inv.app M) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (Qh_restrictCompIso_natIso F G)) M
  simpa using h

omit [DG.DGCategory C] [DG.DGCategory D] [DG.DGCategory E]
  [HasDerivedCategory.{w₁, w} C] [HasDerivedCategory.{w₂, w} D]
  [HasDerivedCategory.{w₃, w} E] in
/-- Composition of restriction on the quotient computes to the original module map. -/
theorem quotient_precompCompIso_hom_app (M : DG.CatModule.{w} E) :
    (HomotopyCategory.precompCompIso F G).hom.app
        ((DG.CatModule.HomotopyCategory.quotient E).obj M) =
      (DG.CatModule.HomotopyCategory.quotient C).map
        ((DG.CatModule.precompCompIso F G).hom.app M) := by
  change 𝟙 _ ≫ (DG.CatModule.HomotopyCategory.quotient C).map
      ((DG.CatModule.precompCompIso F G).hom.app M) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        (HomotopyCategory.precomp F).map (𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  erw [(HomotopyCategory.precomp F).map_id]
  exact Category.comp_id _

open DerivedCategory in
/-- The module comparison has the same components as the homotopy comparison. -/
theorem QCompRestrictIso_hom_app (M : DG.CatModule.{w} D) :
    (QCompRestrictIso F).hom.app M =
      (QhCompRestrictIso F).hom.app ((DG.CatModule.HomotopyCategory.quotient D).obj M) := by
  change 𝟙 _ ≫ (QhCompRestrictIso F).hom.app _ ≫ 𝟙 _ ≫
    DG.CatModule.DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  erw [DG.CatModule.DerivedCategory.Qh.map_id]
  exact Category.comp_id _

open DerivedCategory in
/-- Inverse component formula for the original comparison. -/
theorem QCompRestrictIso_inv_app (M : DG.CatModule.{w} D) :
    (QCompRestrictIso F).inv.app M =
      (QhCompRestrictIso F).inv.app ((DG.CatModule.HomotopyCategory.quotient D).obj M) := by
  have h : (QCompRestrictIso F).app M = (QhCompRestrictIso F).app
      ((DG.CatModule.HomotopyCategory.quotient D).obj M) :=
    Iso.ext (QCompRestrictIso_hom_app F M)
  exact congrArg Iso.inv h

open DerivedCategory in
/-- The actual derived composition comparison on localized dg modules. -/
theorem Q_restrictCompIso_hom_app (M : DG.CatModule.{w} E) :
    (restrictCompIso F G).hom.app (Q.obj M) =
      (QCompRestrictIso (F ⋙ G)).hom.app M ≫
        Q.map ((DG.CatModule.precompCompIso F G).hom.app M) ≫
        (QCompRestrictIso F).inv.app ((DG.CatModule.precomp G).obj M) ≫
        (restrict F).map ((QCompRestrictIso G).inv.app M) := by
  rw [QCompRestrictIso_hom_app, QCompRestrictIso_inv_app, QCompRestrictIso_inv_app]
  have h := Qh_restrictCompIso_hom_app F G ((DG.CatModule.HomotopyCategory.quotient E).obj M)
  rw [quotient_precompCompIso_hom_app] at h
  exact h

instance QCompRestrictIso_commShift :
    NatTrans.CommShift (DerivedCategory.QCompRestrictIso F).hom ℤ := by
  dsimp [DerivedCategory.QCompRestrictIso]
  infer_instance

end OddMath.Frontier.RestrictionCoherence

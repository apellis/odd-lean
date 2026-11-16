import OddMath.SKM.RouquierHomSuperAdjunction

/-! # Unshifted precomposition from one shifted left adjunction

`SwappedHomInversion.md` §1 uses the normalized left adjunction of a single
probe edge. Its precomposition adjunction and signed cap component require
no whole weight-indexed Rouquier family. This is the same shift-square
transport used by `homContentPreAdjunction`, before inserting factor data.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b : B} {E : a ⟶ b} {F : b ⟶ a} {σ : ZMod 2}
  (A : ShiftedSuperAdjunction (k := k) F E σ) (c : B)

/-- Unshifted raising precomposition is left adjoint to shifted lowering,
using exactly the supplied shifted left adjunction and canonical comparisons. -/
def unshiftedPreAdjunction :
    homPre (k := k) (c := c) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ :=
  let S := homParityShift (k := k) (C := a ⟶ c) σ
  let adj : (homPre (k := k) E ⋙ S) ⋙ S ⊣ S ⋙ homPre (k := k) F :=
    (homPreShiftAdjunction A (homParityShiftDatum σ)).comp (homParityShiftAdjunction σ)
  let eL : (homPre (k := k) E ⋙ S) ⋙ S ≅ homPre (k := k) E :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (homParityShiftSquare σ) ≪≫
      Functor.rightUnitor _
  (adj.ofNatIsoLeft eL).ofNatIsoRight (homParityShiftCommute (homPre (k := k) F) σ).symm

private theorem unshiftedPreAdjunction_counit_expansion (H : a ⟶ c) :
    (unshiftedPreAdjunction A c).counit.app H =
      E ◁ (homParityShiftCommute (homPre (k := k) F) σ).hom.app H ≫
      (homParityShiftSquare (k := k) σ).inv.app
        (E ≫ F ≫ (homParityShift (k := k) σ).obj H) ≫
      (homParityShift (k := k) σ).map
        (homPreShiftCounitApp A (homParityShiftDatum σ)
          ((homParityShift (k := k) σ).obj H)) ≫
      (homParityShiftSquare (k := k) σ).hom.app H := by
  simp only [unshiftedPreAdjunction, Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_counit_app]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Functor.comp_obj, Iso.symm_inv]
  change _ ≫ (_ ≫ 𝟙 _) ≫ _ ≫ _ = _
  rw [Category.comp_id, homParityShiftAdjunction_counit_app]
  rfl

/-- The counit has the additional diagonal Koszul factor before the given
normalized cap. No factor of this sign is moved to the left unit. -/
theorem unshiftedPreAdjunction_counit_app (H : a ⟶ c) :
    (unshiftedPreAdjunction A c).counit.app H =
      koszulSign σ σ •
        (E ◁ ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ≫
          (associator E F H).inv ≫ A.counit ▷ H ≫ (leftUnitor H).hom) := by
  let P := homParityShiftDatum (k := k) (C := a ⟶ c) σ
  let S := homParityShift (k := k) (C := a ⟶ c) σ
  rw [unshiftedPreAdjunction_counit_expansion,
    homParityShiftSquare_inv_map_even σ _ H _ (homPreShiftCounitApp_mem A P _)]
  have hn := (homPreShiftCounit A P).naturality (P.iso H).hom
  change S.map (E ◁ F ◁ (P.iso H).hom) ≫ homPreShiftCounitApp A P H =
    homPreShiftCounitApp A P (S.obj H) ≫ (P.iso H).hom at hn
  rw [← hn]
  unfold homPreShiftCounitApp
  rw [reassoc_of% (P.hom_naturality
    (TwoSupercategory.whiskerLeft_mem E
      (TwoSupercategory.whiskerLeft_mem F (P.hom_mem H))))]
  dsimp only [P]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [Iso.inv_hom_id_assoc, homParityShiftCommute_hom_app]
  simp only [homPre, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [← Category.assoc (E ◁ F ◁ _), ← TwoSupercategory.whiskerLeft_comp (R := k),
    ← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
    TwoSupercategory.whiskerLeft_id (R := k), TwoSupercategory.whiskerLeft_id (R := k),
    Category.id_comp, koszulSign_smul (R := k)]

end OddMath.SKM

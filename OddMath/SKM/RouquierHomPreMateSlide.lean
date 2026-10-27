import OddMath.SKM.RouquierHomPreSuperInverse

/-!
# The dot slide of the normalized precomposition mate

`SwappedHomInversion.md`, §2 (1), for the prescribed normalized adjunctions
and the horizontally reversed crossing `-q pre(t)`. The slide is deduced
from the factor's upward relation, not assumed for a principal inverse.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

/-- The specified raw precomposition dot as a supernatural transformation. -/
def homContentPreSuperDot : homContentSuperE T W i muM h ⟶
    homContentSuperE T W i muM h := homPreTransform (T.dot i h) (T.dot_mem i h)

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem preCrossing_slide_app (Z : homWeightSector T.obj W muP muM) :
    ((-koszulSign (D.parity i) (D.parity i)) •
      ((associator (T.E i h₂) (T.E i h) Z).inv ≫
        T.cross i i h₂ h h₂ h ▷ Z ≫ (associator (T.E i h₂) (T.E i h) Z).hom)) ≫
      T.dot i h₂ ▷ (T.E i h ≫ Z) -
    koszulSign (D.parity i) (D.parity i) •
      (T.E i h₂ ◁ (T.dot i h ▷ Z) ≫
        ((-koszulSign (D.parity i) (D.parity i)) •
          ((associator (T.E i h₂) (T.E i h) Z).inv ≫
            T.cross i i h₂ h h₂ h ▷ Z ≫
            (associator (T.E i h₂) (T.E i h) Z).hom))) = 𝟙 _ := by
  have hs := congrArg (fun f => (associator (T.E i h₂) (T.E i h) Z).inv ≫
    f ▷ Z ≫ (associator (T.E i h₂) (T.E i h) Z).hom) (T.loc i h₂ h).slide_left
  simp only [sub_eq_add_neg, TwoSupercategory.add_whiskerRight (R := k),
    TwoSupercategory.neg_whiskerRight (R := k),
    TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k),
    Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_neg,
    Preadditive.neg_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc, Category.id_comp, Iso.inv_hom_id] at hs
  rw [TwoSupercategory.whisker_assoc (R := k)] at hs
  simp only [Category.assoc] at hs
  rw [TwoSupercategory.associator_naturality_left (R := k)] at hs
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, neg_smul,
    Preadditive.comp_neg, Preadditive.neg_comp, smul_neg,
    koszulSign_smul_smul, sub_neg_eq_add, Category.assoc]
  rw [add_comm] at hs
  simpa only [Iso.inv_hom_id_assoc] using hs

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The raw pre-Hom crossing satisfies the required upward slide with RHS one. -/
theorem homContentCrossing_slide :
    homContentCrossing T W i muM h h₂ ≫
        homContentSuperE T W i muM h ◁ homContentPreSuperDot T W i muM h₂ -
      koszulSign (D.parity i) (D.parity i) •
        (homContentPreSuperDot T W i muM h ▷ homContentSuperE T W i muM h₂ ≫
          homContentCrossing T W i muM h h₂) = 𝟙 _ := by
  apply Superfunctor.hom_ext_parity
  all_goals intro Z
  all_goals rcases parity_eq_zero_or_one (D.parity i) with hp | hp
  all_goals simp [sub_eq_add_neg, SCat.comp_app_zero, SCat.comp_app_one,
    homContentCrossing_app, homContentPreSuperDot, homPreTransform,
    SCat.whiskerLeft_app, SCat.whiskerRight_app, homContentSuperE,
    Superfunctor.obj, Superfunctor.map, homPre, hp,
    TwoSupercategory.whiskerLeft_zero (R := k)]
  all_goals simpa only [hp, koszulSign_zero_left, koszulSign_one_one,
    one_smul, neg_smul, neg_neg, Preadditive.neg_comp,
    Preadditive.comp_neg, sub_neg_eq_add, sub_eq_add_neg, Category.assoc] using
      preCrossing_slide_app T W i muM h h₂ Z

/-- The literal normalized pre mate satisfies the slide at every factor height. -/
theorem homContentPreMate_slide :
    rouquierMate (homContentSuperAdjunction T W i muM h)
        (homContentSuperAdjunction T W i muM h₂) (homContentCrossing T W i muM h h₂) ≫
        homContentPreSuperDot T W i muM h₂ ▷ homContentSuperF T W i muM h₂ -
      koszulSign (D.parity i) (D.parity i) •
        (homContentSuperF T W i muM h ◁ homContentPreSuperDot T W i muM h ≫
          rouquierMate (homContentSuperAdjunction T W i muM h)
            (homContentSuperAdjunction T W i muM h₂) (homContentCrossing T W i muM h h₂)) =
      (homContentSuperAdjunction T W i muM h).counit ≫
        (homContentSuperAdjunction T W i muM h₂).unit := by
  simpa only [Int.cast_smul_eq_zsmul] using
    rouquierMate_slide (homContentSuperAdjunction T W i muM h)
      (homContentSuperAdjunction T W i muM h₂)
      (homContentPreSuperDot T W i muM h) (homContentPreSuperDot T W i muM h₂)
      (homContentCrossing T W i muM h h₂) ((koszulSign (D.parity i) (D.parity i) : ℤ) : k)
      (by simpa only [Int.cast_smul_eq_zsmul] using homContentCrossing_slide T W i muM h h₂)

end OddMath.SKM

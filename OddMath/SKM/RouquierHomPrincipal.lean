import OddMath.SKM.RouquierHomMateCoordinates
import OddMath.SKM.RouquierPrincipalWord
/-!
# The normalized principal Hom mate

The even reassociation identifies the raw mate with the principal cup–crossing–cap
word, proving `HomPrincipalMate.md` (10). Its evaluation and the involutive cap
normalization give (1), including the exceptional height-zero scalar. The
comparison uses the specified shifted mate and the inverse-defined `sigL`.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
private theorem closurePrefix {C : Type u} [Bicategory.{w,v} C]
    {a d : C} (Y : a ⟶ a) (Z : a ⟶ d) :
    Bicategory.whiskerRight (Bicategory.leftUnitor Y).inv Z ≫
      (Bicategory.associator (𝟙 a) Y Z).hom =
      (Bicategory.leftUnitor (Y ≫ Z)).inv := by bicategory
private theorem closureMiddle {C : Type u} [Bicategory.{w,v} C]
    {a b d : C} (F : a ⟶ b) (E : b ⟶ a) (Y : a ⟶ a) (Z : a ⟶ d) :
    Bicategory.whiskerRight (Bicategory.associator F E Y).hom Z ≫
      (Bicategory.associator F (E ≫ Y) Z).hom =
    (Bicategory.associator (F ≫ E) Y Z).hom ≫
      (Bicategory.associator F E (Y ≫ Z)).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator E Y Z).inv := by bicategory
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
include k in
private theorem closure_whisker {a b d : B} (F : a ⟶ b) (E : b ⟶ a)
    (Y : a ⟶ a) (Z : a ⟶ d) (U : 𝟙 a ⟶ F ≫ E) (A : E ≫ Y ⟶ E) :
    (leftUnitor (Y ≫ Z)).inv ≫ U ▷ (Y ≫ Z) ≫
      (associator F E (Y ≫ Z)).hom ≫
      F ◁ ((associator E Y Z).inv ≫ A ▷ Z) =
    ((leftUnitor Y).inv ≫ U ▷ Y ≫ (associator F E Y).hom ≫ F ◁ A) ▷ Z ≫
      (associator F E Z).hom := by
  have h₁ := congrArg Subtype.val (closurePrefix
    (Underlying2.hom1 (R := k) Y) (Underlying2.hom1 (R := k) Z))
  have h₂ := congrArg Subtype.val (closureMiddle
    (Underlying2.hom1 (R := k) F) (Underlying2.hom1 (R := k) E)
    (Underlying2.hom1 (R := k) Y) (Underlying2.hom1 (R := k) Z))
  change (leftUnitor Y).inv ▷ Z ≫ (associator (𝟙 a) Y Z).hom =
    (leftUnitor (Y ≫ Z)).inv at h₁
  change (associator F E Y).hom ▷ Z ≫ (associator F (E ≫ Y) Z).hom =
    (associator (F ≫ E) Y Z).hom ≫ (associator F E (Y ≫ Z)).hom ≫
      F ◁ (associator E Y Z).inv at h₂
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [TwoSupercategory.associator_naturality_middle (R := k), reassoc_of% h₂,
    TwoSupercategory.associator_naturality_left_assoc (R := k), reassoc_of% h₁]

private theorem tailPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c d e : C} (E : a ⟶ b) (G : b ⟶ c) (J : c ⟶ d) (Z : d ⟶ e) :
    Bicategory.whiskerLeft E (Bicategory.associator G J Z).inv ≫
      (Bicategory.associator E (G ≫ J) Z).inv ≫
      Bicategory.whiskerRight (Bicategory.associator E G J).inv Z =
    (Bicategory.associator E G (J ≫ Z)).inv ≫
      (Bicategory.associator (E ≫ G) J Z).inv := by bicategory
private theorem tailMiddle {C : Type u} [Bicategory.{w,v} C]
    {a b c d e : C} (E : a ⟶ b) (G : b ⟶ c) (J : c ⟶ d) (Z : d ⟶ e) :
    Bicategory.whiskerRight (Bicategory.associator E G J).hom Z ≫
      (Bicategory.associator E (G ≫ J) Z).hom =
    (Bicategory.associator (E ≫ G) J Z).hom ≫
      (Bicategory.associator E G (J ≫ Z)).hom ≫
      Bicategory.whiskerLeft E (Bicategory.associator G J Z).inv := by bicategory
private theorem tailSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b d : C} (E : a ⟶ b) (Z : b ⟶ d) :
    (Bicategory.associator E (𝟙 b) Z).inv ≫
      Bicategory.whiskerRight (Bicategory.rightUnitor E).hom Z =
    Bicategory.whiskerLeft E (Bicategory.leftUnitor Z).hom := by bicategory
include k in
 private theorem tail_whisker {a b c d : B} (E : a ⟶ b) (G : b ⟶ c) (J : c ⟶ b)
    (Z : b ⟶ d) (t : E ≫ G ⟶ E ≫ G) (V : G ≫ J ⟶ 𝟙 b) :
    E ◁ (associator G J Z).inv ≫ (associator E (G ≫ J) Z).inv ≫
      ((associator E G J).inv ≫ t ▷ J ≫ (associator E G J).hom ≫
        E ◁ V ≫ (rightUnitor E).hom) ▷ Z =
    (associator E G (J ≫ Z)).inv ≫ t ▷ (J ≫ Z) ≫
      (associator E G (J ≫ Z)).hom ≫
      E ◁ ((associator G J Z).inv ≫ V ▷ Z ≫ (leftUnitor Z).hom) := by
  have h₁ := congrArg Subtype.val (tailPrefix
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) G)
    (Underlying2.hom1 (R := k) J) (Underlying2.hom1 (R := k) Z))
  have h₂ := congrArg Subtype.val (tailMiddle
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) G)
    (Underlying2.hom1 (R := k) J) (Underlying2.hom1 (R := k) Z))
  have h₃ := congrArg Subtype.val (tailSuffix
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) Z))
  change E ◁ (associator G J Z).inv ≫ (associator E (G ≫ J) Z).inv ≫
    (associator E G J).inv ▷ Z =
    (associator E G (J ≫ Z)).inv ≫ (associator (E ≫ G) J Z).inv at h₁
  change (associator E G J).hom ▷ Z ≫ (associator E (G ≫ J) Z).hom =
    (associator (E ≫ G) J Z).hom ≫ (associator E G (J ≫ Z)).hom ≫
    E ◁ (associator G J Z).inv at h₂
  change (associator E (𝟙 b) Z).inv ≫ (rightUnitor E).hom ▷ Z =
    E ◁ (leftUnitor Z).hom at h₃
  simp only [TwoSupercategory.comp_whiskerRight (R := k)]
  rw [reassoc_of% h₁, TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, ← TwoSupercategory.associator_inv_naturality_left_assoc (R := k)]
  simp only [Iso.inv_hom_id_assoc]
  rw [h₃]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k)]

include k in
 private theorem cup_naturality {a b d : B} (F : a ⟶ b) (E : b ⟶ a)
    {P Q : a ⟶ d} (U : 𝟙 a ⟶ F ≫ E) {p : ZMod 2}
    (hU : U ∈ parity (R := k) _ _ p) (f : P ⟶ Q)
    (hf : f ∈ parity (R := k) _ _ 0) :
    f ≫ (leftUnitor Q).inv ≫ U ▷ Q ≫ (associator F E Q).hom =
    (leftUnitor P).inv ≫ U ▷ P ≫ (associator F E P).hom ≫ F ◁ E ◁ f := by
  have hh := TwoSupercategory.super_interchange hU hf
  simp only [koszulSign_zero_right, one_smul] at hh
  rw [TwoSupercategory.leftUnitor_inv_naturality_assoc (R := k),
    ← reassoc_of% hh, TwoSupercategory.associator_naturality_right (R := k)]

include k in
 private theorem word_whisker {a b c d : B} (F : a ⟶ b) (E : b ⟶ a)
    (G : a ⟶ c) (J : c ⟶ a) (Z : a ⟶ d)
    (U : 𝟙 a ⟶ F ≫ E) {p : ZMod 2} (hU : U ∈ parity (R := k) _ _ p)
    (t : E ≫ G ⟶ E ≫ G) (V : G ≫ J ⟶ 𝟙 a) :
    (leftUnitor (G ≫ J ≫ Z)).inv ≫ U ▷ (G ≫ J ≫ Z) ≫
      (associator F E (G ≫ J ≫ Z)).hom ≫
      F ◁ ((associator E G (J ≫ Z)).inv ≫ t ▷ (J ≫ Z) ≫
        (associator E G (J ≫ Z)).hom ≫
        E ◁ ((associator G J Z).inv ≫ V ▷ Z ≫ (leftUnitor Z).hom)) =
    (associator G J Z).inv ≫
      ((leftUnitor (G ≫ J)).inv ≫ U ▷ (G ≫ J) ≫
        (associator F E (G ≫ J)).hom ≫
        F ◁ ((associator E G J).inv ≫ t ▷ J ≫ (associator E G J).hom ≫
          E ◁ V ≫ (rightUnitor E).hom)) ▷ Z ≫ (associator F E Z).hom := by
  rw [← closure_whisker (k := k)]
  rw [reassoc_of% (cup_naturality (k := k) F E U hU (associator G J Z).inv
    (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) G J Z)))]
  rw [← TwoSupercategory.whiskerLeft_comp (R := k), tail_whisker (k := k)]
omit [TwoSupercategory k B] in
private theorem family_cup_loc {I X : Type*} [AddCommGroup X] {D : Datum I X}
    (T : RouquierFamily (k := k) (B := B) D) (i : I) {x y z : X}
    (e₁ : x + D.α i = y) (e₂ : y + D.α i = z) :
    T.leftCup i e₁ = (T.loc i e₁ e₂).cupL := by
  subst z
  rfl
omit [TwoSupercategory k B] in
private theorem family_cap_loc {I X : Type*} [AddCommGroup X] {D : Datum I X}
    (T : RouquierFamily (k := k) (B := B) D) (i : I) {x y z : X}
    (e₁ : x + D.α i = y) (e₂ : y + D.α i = z) :
    T.leftCap i e₂ = (T.loc i e₁ e₂).capL := by
  have hx : x = y - D.α i := eq_sub_of_add_eq e₁
  subst x
  rfl
variable
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

/-- The normalized Hom mate is the unnormalized principal word multiplied by
`-s` and the inverse cap scalar at the source of the cap edge. -/
theorem homContentCrossing_coordinates
    (Z : homWeightSector T.obj W nuP muM) :
    let P := homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))
    let P₂ := homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))
    T.E i h ◁ (P.iso (T.F i h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W i muM h)
        (homContentSuperAdjunction T W i muM h₂)
        (homContentCrossing T W i muM h h₂)).app (D.parity i) Z ≫
      (P₂.iso (T.F i h₂ ≫ T.E i h₂ ≫ Z)).hom =
    (-koszulSign (D.parity i) (D.parity i)) •
      (((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k)) •
        ((associator (T.E i h) (T.F i h) Z).inv ≫
          (T.loc i h₂ h).leftCrossingWord ▷ Z ≫
          (associator (T.F i h₂) (T.E i h₂) Z).hom)) := by
  dsimp only
  erw [homContentCrossing_coordinates_raw T W i muM h h₂ Z]
  rw [homContentCrossing_app, ite_eq_left rfl]
  change (leftUnitor (T.E i h ≫ T.F i h ≫ Z)).inv ≫
    T.leftCup i h₂ ▷ (T.E i h ≫ T.F i h ≫ Z) ≫
    (associator (T.F i h₂) (T.E i h₂) (T.E i h ≫ T.F i h ≫ Z)).hom ≫
    T.F i h₂ ◁ (((-koszulSign (D.parity i) (D.parity i)) •
      ((associator (T.E i h₂) (T.E i h) (T.F i h ≫ Z)).inv ≫
        T.cross i i h₂ h h₂ h ▷ (T.F i h ≫ Z) ≫
        (associator (T.E i h₂) (T.E i h) (T.F i h ≫ Z)).hom)) ≫
      T.E i h₂ ◁ ((associator (T.E i h) (T.F i h) Z).inv ≫
        ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫
        (leftUnitor Z).hom)) = _
  simp only [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.smul_whiskerRight, TwoSupercategory.whiskerLeft_smul,
    Linear.comp_smul, Linear.smul_comp]
  simp only [TwoSupercategory.whiskerLeft_zsmul (R := k), Preadditive.comp_zsmul]
  rw [smul_comm]
  congr 2
  rw [SuperRouquierLoc.leftCrossingWord_cap]
  simpa only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    family_cup_loc T i h₂ h, family_cap_loc T i h₂ h] using
    word_whisker (k := k) (T.F i h₂) (T.E i h₂) (T.E i h) (T.F i h) Z
      (T.leftCup i h₂) (T.leftCup_mem i h₂) (T.cross i i h₂ h h₂ h) (T.leftCap i h)
/-- The principal Hom comparison at every height, with `R = -sigL`.
The height-zero coefficient is retained for both parities over any commutative ring. -/
theorem homContentCrossing_principal
    (Z : homWeightSector T.obj W nuP muM) :
    let P := homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))
    let P₂ := homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))
    T.E i h ◁ (P.iso (T.F i h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W i muM h)
        (homContentSuperAdjunction T W i muM h₂)
        (homContentCrossing T W i muM h h₂)).app (D.parity i) Z ≫
      (P₂.iso (T.F i h₂ ≫ T.E i h₂ ≫ Z)).hom =
    (if D.h i (-nuP) = 0 then koszulSign (D.parity i) (D.parity i)
      else koszulSign (D.parity i) (D.parity i * (D.h i (-nuP) : ZMod 2))) •
      ((associator (T.E i h) (T.F i h) Z).inv ≫
        (-(T.loc i h₂ h).sigL) ▷ Z ≫
        (associator (T.F i h₂) (T.E i h₂) Z).hom) := by
  dsimp only
  erw [homContentCrossing_coordinates T W i muM h h₂ Z]
  rw [T.leftCrossingWord_eq, T.leftAdjScalar_inv_coe, Int.cast_smul_eq_zsmul]
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.neg_whiskerRight (R := k), Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Preadditive.comp_neg, Preadditive.neg_comp, smul_smul,
    neg_mul, smul_neg, neg_smul]
  congr 1
  rw [← mul_assoc]
  simpa only [leftAdjParity, Int.cast_add, Int.cast_one] using
    congrArg (fun n : ℤ => n • ((associator (T.E i h) (T.F i h) Z).inv ≫
    (T.loc i h₂ h).sigL ▷ Z ≫ (associator (T.F i h₂) (T.E i h₂) Z).hom))
    (principalWord_scalar (D.parity i) (D.h i (-nuP)))
end OddMath.SKM
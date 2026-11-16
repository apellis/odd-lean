import OddMath.SKM.RouquierFTriangle
/-!
# The unnormalized principal pitchfork word

`HomPrincipalMate.md` §3 (11) evaluates the inverse-defined cup–crossing–cap
word. The signed pitchforks and the canonical F triangle supply its value at
all integer heights. Composition is bottom to top; the crossing has parity p,
and the left cups and caps have parity p(h+1). The two contraction lemmas
retain the corresponding Koszul interchange factors.

The downstream target is the principal Hom mate comparison, §2 (10) and
§3 (16). No substitution into the shifted `rouquierMate`, removal of its
output shifts, matrix inversion, or fusion theorem is asserted here.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
private theorem cupPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) :
    Bicategory.whiskerRight (Bicategory.rightUnitor E).inv F ≫
      (Bicategory.associator E (𝟙 b) F).hom =
      Bicategory.whiskerLeft E (Bicategory.leftUnitor F).inv := by bicategory
private theorem cupMiddle {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) :
    (Bicategory.associator E (F ≫ E) F).inv ≫
      Bicategory.whiskerRight (Bicategory.associator E F E).inv F ≫
      (Bicategory.associator (E ≫ F) E F).hom ≫
      (Bicategory.associator E F (E ≫ F)).hom =
      Bicategory.whiskerLeft E (Bicategory.associator F E F).hom := by bicategory
private theorem cupSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) :
    (Bicategory.associator E F (𝟙 a)).inv ≫ (Bicategory.rightUnitor (E ≫ F)).hom =
      Bicategory.whiskerLeft E (Bicategory.rightUnitor F).hom := by bicategory
private theorem capPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) :
    (Bicategory.leftUnitor (F ≫ E)).inv ≫ (Bicategory.associator (𝟙 b) F E).inv =
      Bicategory.whiskerRight (Bicategory.leftUnitor F).inv E := by bicategory
private theorem capMiddle {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) :
    (Bicategory.associator (F ≫ E) F E).hom ≫
      (Bicategory.associator F E (F ≫ E)).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator E F E).inv =
      Bicategory.whiskerRight (Bicategory.associator F E F).hom E ≫
      (Bicategory.associator F (E ≫ F) E).hom := by bicategory
private theorem capSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) :
    (Bicategory.associator F (𝟙 a) E).inv ≫
      Bicategory.whiskerRight (Bicategory.rightUnitor F).hom E =
      Bicategory.whiskerLeft F (Bicategory.leftUnitor E).hom := by bicategory
private theorem wordPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} (G : a ⟶ b) (H : b ⟶ c) :
    (Bicategory.leftUnitor (G ≫ H)).inv ≫ (Bicategory.associator (𝟙 a) G H).inv =
      Bicategory.whiskerRight (Bicategory.leftUnitor G).inv H := by bicategory
private theorem wordMiddle {C : Type u} [Bicategory.{w,v} C]
    {a b c d e : C} (F : a ⟶ b) (E : b ⟶ c) (G : c ⟶ d) (H : d ⟶ e) :
    (Bicategory.associator (F ≫ E) G H).hom ≫
      (Bicategory.associator F E (G ≫ H)).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator E G H).inv =
      Bicategory.whiskerRight (Bicategory.associator F E G).hom H ≫
      (Bicategory.associator F (E ≫ G) H).hom := by bicategory
private theorem wordMiddleInv {C : Type u} [Bicategory.{w,v} C]
    {a b c d e : C} (F : a ⟶ b) (E : b ⟶ c) (G : c ⟶ d) (H : d ⟶ e) :
    (Bicategory.associator F (E ≫ G) H).inv ≫
      Bicategory.whiskerRight (Bicategory.associator F E G).inv H ≫
      (Bicategory.associator (F ≫ E) G H).hom ≫
      (Bicategory.associator F E (G ≫ H)).hom =
      Bicategory.whiskerLeft F (Bicategory.associator E G H).hom := by bicategory
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private theorem rightClosure {a b : B} {E : a ⟶ b} {F : b ⟶ a}
    {X : a ⟶ a} (U : 𝟙 b ⟶ F ≫ E) (V : E ≫ F ⟶ 𝟙 a)
    {p q : ZMod 2} (l : E ≫ F ⟶ X)
    (hl : l ∈ parity (R := k) _ _ p) (hV : V ∈ parity (R := k) _ _ q) :
    ((rightUnitor E).inv ≫ E ◁ U ≫ (associator E F E).inv ≫ l ▷ E) ▷ F ≫
      (associator X E F).hom ≫ X ◁ V ≫ (rightUnitor X).hom =
    koszulSign p q • ((E ◁ ((leftUnitor F).inv ≫ U ▷ F ≫
      (associator F E F).hom ≫ F ◁ V ≫ (rightUnitor F).hom)) ≫ l) := by
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  rw [TwoSupercategory.associator_naturality_left_assoc (R := k)]
  rw [reassoc_of% (TwoSupercategory.super_interchange hl hV)]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    TwoSupercategory.whiskerRight_id (R := k), Category.assoc]
  congr 1
  rw [TwoSupercategory.comp_whiskerLeft (R := k)]
  simp only [Category.assoc]
  rw [TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc]
  have h₁ := congrArg Subtype.val (cupPrefix
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F))
  have h₂ := congrArg Subtype.val (cupMiddle
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F))
  have h₃ := congrArg Subtype.val (cupSuffix
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F))
  change (rightUnitor E).inv ▷ F ≫ (associator E (𝟙 b) F).hom =
    E ◁ (leftUnitor F).inv at h₁
  change (associator E (F ≫ E) F).inv ≫ (associator E F E).inv ▷ F ≫
    (associator (E ≫ F) E F).hom ≫ (associator E F (E ≫ F)).hom =
    E ◁ (associator F E F).hom at h₂
  change (associator E F (𝟙 a)).inv ≫ (rightUnitor (E ≫ F)).hom =
    E ◁ (rightUnitor F).hom at h₃
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem leftClosure {a b : B} {E : a ⟶ b} {F : b ⟶ a}
    {Y : b ⟶ b} (U : 𝟙 b ⟶ F ≫ E) (V : E ≫ F ⟶ 𝟙 a)
    {p q : ZMod 2} (l : Y ⟶ F ≫ E)
    (hU : U ∈ parity (R := k) _ _ q) (hl : l ∈ parity (R := k) _ _ p) :
    (leftUnitor Y).inv ≫ U ▷ Y ≫ (associator F E Y).hom ≫
      F ◁ (E ◁ l ≫ (associator E F E).inv ≫ V ▷ E ≫ (leftUnitor E).hom) =
    koszulSign q p • (l ≫ ((leftUnitor F).inv ≫ U ▷ F ≫
      (associator F E F).hom ≫ F ◁ V ≫ (rightUnitor F).hom) ▷ E) := by
  simp only [TwoSupercategory.whiskerLeft_comp (R := k)]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k)]
  rw [reassoc_of% (TwoSupercategory.super_interchange hU hl)]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    TwoSupercategory.id_whiskerLeft (R := k), Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc]
  have h₁ := congrArg Subtype.val (capPrefix
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F))
  have h₂ := congrArg Subtype.val (capMiddle
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F))
  have h₃ := congrArg Subtype.val (capSuffix
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F))
  change (leftUnitor (F ≫ E)).inv ≫ (associator (𝟙 b) F E).inv =
    (leftUnitor F).inv ▷ E at h₁
  change (associator (F ≫ E) F E).hom ≫ (associator F E (F ≫ E)).hom ≫
    F ◁ (associator E F E).inv =
    (associator F E F).hom ▷ E ≫ (associator F (E ≫ F) E).hom at h₂
  change (associator F (𝟙 a) E).inv ≫ (rightUnitor F).hom ▷ E =
    F ◁ (leftUnitor E).hom at h₃
  rw [reassoc_of% h₁, reassoc_of% h₂]
  simp only [TwoSupercategory.comp_whiskerRight (R := k)]
  rw [TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc]
  rw [h₃]

namespace SuperRouquierLoc
variable {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {A₃ : SuperAdjunction (k := k) E₃ F₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t' : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}
  {p : ZMod 2} {h h' : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
  (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t' p h')

/-- The unnormalized word of HomPrincipalMate.md (9), with explicit coherence. -/
def leftCrossingWord : E₂ ≫ F₂ ⟶ F₁ ≫ E₁ :=
  ((leftUnitor E₂).inv ≫ L.cupL ▷ E₂ ≫ (associator F₁ E₁ E₂).hom ≫
    F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv) ▷ F₂ ≫
    (associator (F₁ ≫ E₁) E₂ F₂).hom ≫ (F₁ ≫ E₁) ◁ L.capL ≫
      (rightUnitor (F₁ ≫ E₁)).hom

/-- Reassociate the same word so the negative cap pitchfork is contiguous. -/
theorem leftCrossingWord_cap : L.leftCrossingWord =
    (leftUnitor (E₂ ≫ F₂)).inv ≫ L.cupL ▷ (E₂ ≫ F₂) ≫
      (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫
      F₁ ◁ ((associator E₁ E₂ F₂).inv ≫ t ▷ F₂ ≫
        (associator E₁ E₂ F₂).hom ≫ E₁ ◁ L.capL ≫ (rightUnitor E₁).hom) := by
  have h₁ := congrArg Subtype.val (wordPrefix
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂))
  have h₂ := congrArg Subtype.val (wordMiddle
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂))
  have h₃ := congrArg Subtype.val (wordMiddleInv
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) E₂) (Underlying2.hom1 (R := k) F₂))
  have h₄ := congrArg Subtype.val (cupSuffix
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₁))
  change (leftUnitor (E₂ ≫ F₂)).inv ≫ (associator (𝟙 b) E₂ F₂).inv =
    (leftUnitor E₂).inv ▷ F₂ at h₁
  change (associator (F₁ ≫ E₁) E₂ F₂).hom ≫
    (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫ F₁ ◁ (associator E₁ E₂ F₂).inv =
    (associator F₁ E₁ E₂).hom ▷ F₂ ≫ (associator F₁ (E₁ ≫ E₂) F₂).hom at h₂
  change (associator F₁ (E₁ ≫ E₂) F₂).inv ≫ (associator F₁ E₁ E₂).inv ▷ F₂ ≫
    (associator (F₁ ≫ E₁) E₂ F₂).hom ≫ (associator F₁ E₁ (E₂ ≫ F₂)).hom =
    F₁ ◁ (associator E₁ E₂ F₂).hom at h₃
  change (associator F₁ E₁ (𝟙 b)).inv ≫ (rightUnitor (F₁ ≫ E₁)).hom =
    F₁ ◁ (rightUnitor E₁).hom at h₄
  simp only [leftCrossingWord, TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂,
    TwoSupercategory.whisker_assoc (R := k), TwoSupercategory.comp_whiskerLeft (R := k)]
  simp only [Category.assoc]
  rw [reassoc_of% h₃, h₄]

include U in
/-- Positive and zero heights retain the exceptional cup-pitchfork coefficient. -/
theorem leftCrossingWord_of_nonneg (hw : h' = h + 2) (hh : 0 ≤ h)
    (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
    (hB : E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t' =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    L.leftCrossingWord = (if h = 0 then 1 else koszulSign p p) • L.sigL := by
  rw [leftCrossingWord, L.cupL_pitchfork_of_nonneg U hw hh hsq hsq' hB]
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k), Preadditive.zsmul_comp]
  rw [rightClosure U.cupL L.capL L.sigL L.sigL_mem L.capL_mem,
    L.leftAdj_triangle_F U hw hsq hsq' hB]
  simp only [TwoSupercategory.whiskerLeft_zsmul (R := k),
    TwoSupercategory.whiskerLeft_id (R := k), Preadditive.zsmul_comp,
    Category.id_comp, smul_smul]
  congr 1
  rw [ite_eq_right (show ¬ h < 0 by omega), Int.cast_add, Int.cast_one]
  generalize (h : ZMod 2) = q
  split_ifs with hz
  all_goals fin_cases p <;> fin_cases q <;> decide

include L in
/-- The negative pitchfork gives coefficient one also at upper height zero. -/
theorem leftCrossingWord_of_nonpos (hw : h' = h + 2) (hh : h < -1)
    (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
    (hB : E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t' =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    U.leftCrossingWord = U.sigL := by
  rw [U.leftCrossingWord_cap, L.capL_pitchfork_below_neg_one U hw hh hsq hsq' hB,
    leftClosure U.cupL L.capL U.sigL U.cupL_mem U.sigL_mem,
    L.leftAdj_triangle_F U hw hsq hsq' hB]
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k), Preadditive.comp_zsmul,
    Category.comp_id, smul_smul]
  have hs : koszulSign (p * ((h' : ZMod 2) + 1)) p *
      (koszulSign (p * ((h + 1 : ℤ) : ZMod 2)) (p * ((h + 1 : ℤ) : ZMod 2)) *
        (if h < 0 then 1 else koszulSign p p)) = 1 := by
    rw [ite_eq_left (show h < 0 by omega), hw]
    simp only [Int.cast_add, Int.cast_one]
    generalize (h : ZMod 2) = q
    fin_cases p <;> fin_cases q <;> decide
  rw [hs, one_smul]
end SuperRouquierLoc
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D)

/-- HomPrincipalMate.md §3 (11): the unnormalized word at every integer height.
This is not yet an identification with the shifted Hom partial mate. -/
theorem leftCrossingWord_eq (i : I) {x y z : X}
    (e₁ : x + D.α i = y) (e₂ : y + D.α i = z) :
    (T.loc i e₁ e₂).leftCrossingWord =
      (if D.h i y ≤ 0 then 1 else koszulSign (D.parity i) (D.parity i)) •
        (T.loc i e₁ e₂).sigL := by
  by_cases hh : D.h i y ≤ 0
  · have hw : D.h i y = D.h i x + 2 := by
      rw [← e₁]
      simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]
    have ht := (T.loc i (sub_add_cancel x (D.α i)) e₁).leftCrossingWord_of_nonpos
      (T.loc i e₁ e₂) hw (by omega)
      (T.square i (sub_add_cancel x (D.α i)) e₁) (T.square i e₁ e₂)
      (T.braid i (sub_add_cancel x (D.α i)) e₁ e₂)
    simpa only [ite_eq_left hh, one_smul] using ht
  · have hw : D.h i z = D.h i y + 2 := by
      rw [← e₂]
      simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]
    have ht := (T.loc i e₁ e₂).leftCrossingWord_of_nonneg (T.loc i e₂ rfl)
      hw (by omega) (T.square i e₁ e₂) (T.square i e₂ rfl) (T.braid i e₁ e₂ rfl)
    simpa only [ite_eq_right hh, ite_eq_right (show D.h i y ≠ 0 by omega)] using ht
end RouquierFamily

/-- HomPrincipalMate.md §3 (16): the scalar remaining after the proposed Hom
shift removal, using the involutive cap normalization c(h). In particular the
nonzero-height expression cannot replace the exceptional height-zero value. -/
theorem principalWord_scalar (p : ZMod 2) (h : ℤ) :
    koszulSign p p *
      (koszulSign (p * ((h + 1 : ℤ) : ZMod 2)) (p * ((h + 1 : ℤ) : ZMod 2)) *
        (if h < 0 then 1 else koszulSign p p)) *
      (if h ≤ 0 then 1 else koszulSign p p) =
    if h = 0 then koszulSign p p else koszulSign p (p * (h : ZMod 2)) := by
  by_cases hz : h = 0
  · subst h
    fin_cases p <;> decide
  · rw [ite_eq_right hz]
    by_cases hn : h < 0
    · rw [ite_eq_left hn, ite_eq_left (by omega)]
      simp only [Int.cast_add, Int.cast_one]
      generalize (h : ZMod 2) = q
      fin_cases p <;> fin_cases q <;> decide
    · rw [ite_eq_right hn, ite_eq_right (by omega)]
      simp only [Int.cast_add, Int.cast_one]
      generalize (h : ZMod 2) = q
      fin_cases p <;> fin_cases q <;> decide
end OddMath.SKM

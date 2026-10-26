import OddMath.SKM.RouquierHomPostCoordinates
/-!
# The principal content-shifted postcomposition mate

The principal equality of `HomProbeMatrix.md` (B) holds for the specified
beta/xi crossing and the input-shifted right adjoint. Two shift exchanges
cancel on the crossing. Unit and counit coordinates remove the remaining
endpoint comparisons; even bicategorical coherence identifies the resulting
word with postcomposition by the factor mixed mate.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v r
variable {k : Type r} [CommRing k]
  {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D] [PiSupercategory k D]
  (F : C ⥤ C) (G : C ⥤ D) (N : D ⥤ C)
  [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  [N.Additive] [N.Linear k] [IsSuperfunctor k N]
  (p q : ZMod 2) (t : ∀ Z, (F ⋙ G).obj Z ⟶ (F ⋙ G).obj Z)
  (ht : IsSupernatural k q t) (Z : C)

include ht in
private theorem shift_word_conjugate :
    let S := homParityShift (k := k) p
    let a := homShiftConjugationIso F p Z
    let Q := F.obj (S.obj Z)
    let theta := homShiftConjugationIso (k := k) G p Q
    (homParityShiftSquare (k := k) p).inv.app (G.obj (S.obj Q)) ≫
      (homParityShift (k := k) p).map (theta.hom ≫ t (S.obj Z) ≫ theta.inv) ≫
      (homParityShiftSquare (k := k) p).hom.app (G.obj (S.obj Q)) ≫ G.map a.hom =
      G.map a.hom ≫ t Z := by
  dsimp only
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (homShiftConjugationIso_unit_cancel G p (F.obj ((homParityShift (k := k) p).obj Z)))]
  have hc := homShiftConjugationIso_comp (k := k) F G p Z
  have hn := homShiftConjugationIso_supernatural (F ⋙ G) (F ⋙ G) p q t ht Z
  rw [hc] at hn
  have hi : (homParityShift (k := k) p).map
      (homShiftConjugationIso (k := k) G p (F.obj ((homParityShift (k := k) p).obj Z))).inv ≫
      (homParityShiftSquare (k := k) p).hom.app
        (G.obj ((homParityShift (k := k) p).obj (F.obj ((homParityShift (k := k) p).obj Z)))) =
      (homParityShiftCommute G p).hom.app (F.obj ((homParityShift (k := k) p).obj Z)) := by
    apply (cancel_epi ((homParityShift (k := k) p).map
      (homShiftConjugationIso (k := k) G p (F.obj ((homParityShift (k := k) p).obj Z))).hom)).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    apply (cancel_epi ((homParityShiftSquare (k := k) p).inv.app _)).mp
    rw [reassoc_of% (homShiftConjugationIso_unit_cancel (k := k) G p
      (F.obj ((homParityShift (k := k) p).obj Z)))]
    simp
  rw [reassoc_of% hi]
  simp only [Category.assoc] at hn
  rw [hn]
  simp
omit [N.Additive] [N.Linear k] [IsSuperfunctor k N] in
include ht in
private theorem shift_mate_word (u : 𝟭 C ⟶ G ⋙ N) (v : F ⟶ 𝟭 C) :
    let S := homParityShift (k := k) p
    let SD := homParityShift (k := k) (C := D) p
    let a := homShiftConjugationIso F p Z
    let Q := F.obj (S.obj Z)
    let theta := homShiftConjugationIso G p Q
    a.inv ≫ u.app (S.obj Q) ≫
      N.map ((homParityShiftSquare (k := k) p).inv.app (G.obj (S.obj Q))) ≫
      N.map (SD.map (theta.hom ≫ t (S.obj Z) ≫ theta.inv)) ≫
      N.map (SD.map (SD.map (G.map (a.hom ≫ v.app Z)))) ≫
      N.map ((homParityShiftSquare (k := k) p).hom.app (G.obj Z)) =
    u.app (F.obj Z) ≫ N.map (t Z) ≫ N.map (G.map (v.app Z)) := by
  dsimp only
  have hn := (homParityShiftSquare (k := k) p).hom.naturality
    (G.map ((homShiftConjugationIso (k := k) F p Z).hom ≫ v.app Z))
  change (homParityShift (k := k) p).map
      ((homParityShift (k := k) p).map (G.map ((homShiftConjugationIso (k := k) F p Z).hom ≫ v.app Z))) ≫
      (homParityShiftSquare (k := k) p).hom.app (G.obj Z) =
    (homParityShiftSquare (k := k) p).hom.app _ ≫
      G.map ((homShiftConjugationIso (k := k) F p Z).hom ≫ v.app Z) at hn
  rw [← N.map_comp, hn, G.map_comp]
  simp only [← N.map_comp]
  rw [reassoc_of% (shift_word_conjugate F G p q t ht Z)]
  rw [N.map_comp, N.map_comp]
  have hu := u.naturality (homShiftConjugationIso (k := k) F p Z).hom
  change _ ≫ u.app _ = u.app _ ≫ N.map (G.map _) at hu
  rw [← reassoc_of% hu]
  simp
end OddMath.SKM
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
private theorem postPrefix {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (Z : a ⟶ c) (F : c ⟶ b) (E : b ⟶ c) (G : c ⟶ d) (J : d ⟶ c)
    (U : 𝟙 c ⟶ G ≫ J) :
    (Bicategory.rightUnitor ((Z ≫ F) ≫ E)).inv ≫
      Bicategory.whiskerLeft ((Z ≫ F) ≫ E) U ≫
      (Bicategory.associator ((Z ≫ F) ≫ E) G J).inv ≫
      Bicategory.whiskerRight (Bicategory.associator (Z ≫ F) E G).hom J ≫
      (Bicategory.associator (Z ≫ F) (E ≫ G) J).hom ≫
      (Bicategory.associator Z F ((E ≫ G) ≫ J)).hom =
    (Bicategory.associator Z F E).hom ≫
      Bicategory.whiskerLeft Z ((Bicategory.rightUnitor (F ≫ E)).inv ≫
        Bicategory.whiskerLeft (F ≫ E) U ≫
        (Bicategory.associator F E (G ≫ J)).hom ≫
        Bicategory.whiskerLeft F (Bicategory.associator E G J).inv) := by bicategory
private theorem postSuffix {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (Z : a ⟶ c) (F : c ⟶ b) (E : b ⟶ c) (G : c ⟶ d) (J : d ⟶ c)
    (V : F ≫ E ⟶ 𝟙 c) :
    (Bicategory.associator (Z ≫ F) (E ≫ G) J).hom ≫
      (Bicategory.associator Z F ((E ≫ G) ≫ J)).hom ≫
      Bicategory.whiskerLeft Z ((Bicategory.associator F (E ≫ G) J).inv ≫
        Bicategory.whiskerRight (Bicategory.associator F E G).inv J ≫
        Bicategory.whiskerRight (Bicategory.whiskerRight V G) J ≫
        Bicategory.whiskerRight (Bicategory.leftUnitor G).hom J) ≫
      (Bicategory.associator Z G J).inv =
    Bicategory.whiskerRight (Bicategory.associator (Z ≫ F) E G).inv J ≫
      Bicategory.whiskerRight (Bicategory.whiskerRight
        ((Bicategory.associator Z F E).hom ≫ Bicategory.whiskerLeft Z V ≫
          (Bicategory.rightUnitor Z).hom) G) J := by bicategory
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
private theorem post_mate_word {a b c d : B} (Z : a ⟶ c)
    {F : c ⟶ b} {E : b ⟶ c} {G : c ⟶ d} {J : d ⟶ c}
    (A : SuperAdjunction (k := k) E F) (A' : SuperAdjunction (k := k) G J)
    (t : E ≫ G ⟶ E ≫ G) :
    (homPostUnit A').app ((Z ≫ F) ≫ E) ≫
      ((associator (Z ≫ F) E G).hom ≫ (Z ≫ F) ◁ t ≫
        (associator (Z ≫ F) E G).inv) ▷ J ≫
      ((homPostCounit A).app Z ▷ G) ▷ J =
    (associator Z F E).hom ≫ Z ◁ rouquierMate A A' t ≫ (associator Z G J).inv := by
  have hp := congrArg Subtype.val (postPrefix
    (Underlying2.hom1 (R := k) Z) (Underlying2.hom1 (R := k) F)
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) G)
    (Underlying2.hom1 (R := k) J) ⟨A'.unit, A'.unit_mem⟩)
  have hs := congrArg Subtype.val (postSuffix
    (Underlying2.hom1 (R := k) Z) (Underlying2.hom1 (R := k) F)
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) G)
    (Underlying2.hom1 (R := k) J) ⟨A.counit, A.counit_mem⟩)
  change (rightUnitor ((Z ≫ F) ≫ E)).inv ≫ ((Z ≫ F) ≫ E) ◁ A'.unit ≫
    (associator ((Z ≫ F) ≫ E) G J).inv ≫ (associator (Z ≫ F) E G).hom ▷ J ≫
    (associator (Z ≫ F) (E ≫ G) J).hom ≫
    (associator Z F ((E ≫ G) ≫ J)).hom =
    (associator Z F E).hom ≫ Z ◁ ((rightUnitor (F ≫ E)).inv ≫
      (F ≫ E) ◁ A'.unit ≫ (associator F E (G ≫ J)).hom ≫
      F ◁ (associator E G J).inv) at hp
  change (associator (Z ≫ F) (E ≫ G) J).hom ≫
    (associator Z F ((E ≫ G) ≫ J)).hom ≫
    Z ◁ ((associator F (E ≫ G) J).inv ≫ (associator F E G).inv ▷ J ≫
      (A.counit ▷ G) ▷ J ≫ (leftUnitor G).hom ▷ J) ≫
    (associator Z G J).inv =
    (associator (Z ≫ F) E G).inv ▷ J ≫
      (((associator Z F E).hom ≫ Z ◁ A.counit ≫ (rightUnitor Z).hom) ▷ G) ▷ J at hs
  dsimp [homPostUnit, homPostCounit, homPostComp, homPostId,
    homPostTransform, SuperNatTrans.toNatTrans]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc] at hs ⊢
  rw [← hs]
  rw [TwoSupercategory.associator_naturality_middle_assoc (R := k),
    TwoSupercategory.associator_naturality_right_assoc (R := k)]
  rw [reassoc_of% hp]
  simp only [rouquierMate, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
end OddMath.SKM
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe w
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM rhoM : X}
  (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem post_raw_supernatural :
    IsSupernatural k (D.parity i)
      (F := (homPost (k := k) (a := T (-muP)) (W.F i h) ⋙ homPost (k := k) (W.E i h)) ⋙
        homPost (k := k) (W.E i h₂))
      (G := (homPost (k := k) (a := T (-muP)) (W.F i h) ⋙ homPost (k := k) (W.E i h)) ⋙
        homPost (k := k) (W.E i h₂))
      (fun Z => (associator (Z ≫ W.F i h) (W.E i h) (W.E i h₂)).hom ≫
        (Z ≫ W.F i h) ◁ W.cross i i h h₂ h h₂ ≫
        (associator (Z ≫ W.F i h) (W.E i h) (W.E i h₂)).inv) := by
  have ha := isSupernatural_of_natTrans (homPostComp (k := k) (a := T (-muP))
    (W.E i h) (W.E i h₂)).hom
    (fun Z => TwoSupercategory.associator_hom_mem (R := k) Z _ _)
  have hb := isSupernatural_of_natTrans (homPostComp (k := k) (a := T (-muP))
    (W.E i h) (W.E i h₂)).inv
    (fun Z => inv_mem (associator Z _ _) (TwoSupercategory.associator_hom_mem (R := k) Z _ _))
  have ht := (homPostTransform (k := k) (a := T (-muP))
    (W.cross i i h h₂ h h₂) (W.loc i h h₂).cross_mem).isSupernatural (D.parity i)
  have hh := (ha.comp (ht.comp hb)).whiskerLeft (homPost (k := k) (W.F i h))
  simpa [homPostComp, homPostTransform, homPost] using hh

private theorem post_coordinates_raw (Z : homWeightSector T W.obj muP nuM) :
  (homContentPostSourceIso T W i betaP muP h Z).inv ≫
    (rouquierMate (homContentPostSuperAdjunction T W i betaP muP h)
      (homContentPostSuperAdjunction T W i betaP muP h₂)
      (homContentPostCrossing T W i betaP muP h h₂)).app (D.parity i) Z ≫
    (homContentPostTargetIso T W i betaP muP h₂ Z).hom =
  (homPostUnit (W.adj i h₂)).app ((Z ≫ W.F i h) ≫ W.E i h) ≫
    ((associator (Z ≫ W.F i h) (W.E i h) (W.E i h₂)).hom ≫
      (Z ≫ W.F i h) ◁ W.cross i i h h₂ h h₂ ≫
      (associator (Z ≫ W.F i h) (W.E i h) (W.E i h₂)).inv) ▷ W.F i h₂ ≫
    ((homPostCounit (W.adj i h)).app Z ▷ W.E i h₂) ▷ W.F i h₂ := by
  rw [rouquierMate_scat_app]
  change _ ≫ ((homContentPostAdjunction T W i betaP muP h₂).unit.app _ ≫
    (homContentPostF T W i betaP muP h₂).map
      ((homContentPostCrossing T W i betaP muP h h₂).app (D.parity i) _) ≫
    (homContentPostF T W i betaP muP h₂).map
      ((homContentPostE T W i betaP muP h₂).map
        ((homContentPostAdjunction T W i betaP muP h).counit.app Z))) ≫ _ = _
  rw [homContentPostAdjunction_unit_coordinates,
    homContentPostAdjunction_counit_coordinates, homContentPostCrossing_app, ite_eq_left rfl]
  have hw := shift_mate_word
    (homPost (k := k) (a := T (-muP)) (W.F i h) ⋙ homPost (k := k) (W.E i h))
    (homPost (k := k) (W.E i h₂)) (homPost (k := k) (W.F i h₂))
    (homContentShift D i betaP) (D.parity i) _
    (post_raw_supernatural T W i muP h h₂) Z (homPostUnit (W.adj i h₂))
    (homPostCounit (W.adj i h))
  simpa [homContentPostWordIso, homShiftConjugationNatIso, homShiftConjugationIso,
    homContentPostSourceIso, homContentPostTargetIso, homContentPostSuperE,
    homContentPostE, homContentPostF, homPostComp, homPost,
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc] using hw

/-- The principal postcomposition comparison, for every content and both colour parities.
The crossing and both adjunctions are the specified content-shifted ones. -/
theorem homContentPostCrossing_principal (Z : homWeightSector T W.obj muP nuM) :
  (homContentPostSourceIso T W i betaP muP h Z).inv ≫
    (rouquierMate (homContentPostSuperAdjunction T W i betaP muP h)
      (homContentPostSuperAdjunction T W i betaP muP h₂)
      (homContentPostCrossing T W i betaP muP h h₂)).app (D.parity i) Z ≫
    (homContentPostTargetIso T W i betaP muP h₂ Z).hom =
  (associator Z (W.F i h) (W.E i h)).hom ≫
    Z ◁ (W.loc i h h₂).sig ≫
    (associator Z (W.E i h₂) (W.F i h₂)).inv := by
  rw [post_coordinates_raw]
  exact post_mate_word Z (W.adj i h) (W.adj i h₂) (W.cross i i h h₂ h h₂)
end OddMath.SKM

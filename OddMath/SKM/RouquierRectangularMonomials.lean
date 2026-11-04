import OddMath.SKM.RouquierRectangularComposition

/-! # Separated monomials under rectangular bending

The correction terms in Brundan–Ellis Lemma 3.3, used in the
cap tests of Lemma 7.1, separate into a dotted cap, a middle
endomorphism, and a dotted cup. Both bends are the prescribed even
right adjunctions; the order of the three endomorphisms is retained.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem rectangularSeparatedCap {C : Type u} [Bicategory.{w,v} C]
    {a b c d : C} (E : a ⟶ b) (F : b ⟶ a) (G : b ⟶ c)
    (H : c ⟶ d) (ε : F ≫ E ⟶ 𝟙 b) :
    (Bicategory.associator F (E ≫ G) H).hom ≫
      Bicategory.whiskerLeft F (Bicategory.associator E G H).hom ≫
      (Bicategory.associator F E (G ≫ H)).inv ≫
      Bicategory.whiskerRight ε (G ≫ H) ≫
      (Bicategory.leftUnitor (G ≫ H)).hom =
    Bicategory.whiskerRight
      ((Bicategory.associator F E G).inv ≫ Bicategory.whiskerRight ε G ≫
        (Bicategory.leftUnitor G).hom) H := by bicategory

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- Bending the associator separates the given cap and cup. -/
theorem rectangularMate_associator {a b c d : B}
    {E : a ⟶ b} {F : b ⟶ a} (G : b ⟶ c) {H : c ⟶ d} {K : d ⟶ c}
    (A : SuperAdjunction (k := k) E F) (C : SuperAdjunction (k := k) H K) :
    rectangularMate A C (E ≫ G) (G ≫ H) (associator E G H).hom =
      (associator F E G).inv ≫ A.counit ▷ G ≫ (leftUnitor G).hom ≫
      (rightUnitor G).inv ≫ G ◁ C.unit ≫ (associator G H K).inv := by
  have hb := congrArg Subtype.val (rectangularSeparatedCap
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F)
    (Underlying2.hom1 (R := k) G) (Underlying2.hom1 (R := k) H)
    ⟨A.counit, A.counit_mem⟩)
  change (associator F (E ≫ G) H).hom ≫ F ◁ (associator E G H).hom ≫
    (associator F E (G ≫ H)).inv ≫ A.counit ▷ (G ≫ H) ≫
    (leftUnitor (G ≫ H)).hom =
    ((associator F E G).inv ≫ A.counit ▷ G ≫ (leftUnitor G).hom) ▷ H at hb
  rw [rectangularMate_postTranspose, hb]
  have hn := (homPostAdjunction C).homEquiv_naturality_left
    ((associator F E G).inv ≫ A.counit ▷ G ≫ (leftUnitor G).hom) (𝟙 (G ≫ H))
  simpa [homPost, CategoryTheory.Adjunction.homEquiv, homPostAdjunction,
    homPostUnit, homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans,
    Category.assoc, TwoSupercategory.id_whiskerRight (R := k),
    TwoSupercategory.comp_whiskerRight (R := k)] using hn

/-- Ordered separated endomorphisms bend to a cap, middle map and cup,
with no extra homogeneity hypothesis. -/
theorem rectangularMate_separated {a b c d : B}
    {E : a ⟶ b} {F : b ⟶ a} (G : b ⟶ c) {H : c ⟶ d} {K : d ⟶ c}
    (A : SuperAdjunction (k := k) E F) (C : SuperAdjunction (k := k) H K)
    (x : E ⟶ E) (y : G ⟶ G) (z : H ⟶ H) :
    (associator F E G).hom ≫
      rectangularMate A C (E ≫ G) (G ≫ H)
        ((x ▷ G) ▷ H ≫ (associator E G H).hom ≫ E ◁ (y ▷ H ≫ G ◁ z)) ≫
      (associator G H K).hom =
    (F ◁ x ≫ A.counit) ▷ G ≫ (leftUnitor G).hom ≫ y ≫
      (rightUnitor G).inv ≫ G ◁ (C.unit ≫ z ▷ K) := by
  have hn := (homPostUnit C).naturality y
  change y ≫ ((rightUnitor G).inv ≫ G ◁ C.unit ≫ (associator G H K).inv) =
    ((rightUnitor G).inv ≫ G ◁ C.unit ≫ (associator G H K).inv) ≫ (y ▷ H) ▷ K at hn
  rw [rectangularMate_left, rectangularMate_right, rectangularMate_associator]
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [TwoSupercategory.associator_inv_naturality_middle_assoc (R := k)]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hn]
  rw [TwoSupercategory.associator_naturality_middle (R := k)]
  simp only [Iso.inv_hom_id_assoc]

end OddMath.SKM

import OddMath.SKM.RouquierHom
import StringDiagrams.Super.UnderlyingBicategory
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat

/-!
# Adjunction transport for super Hom sectors

Ports the postcomposition adjunction used by
`Categorification/TwoRep/RouqProduct.lean`. The even underlying bicategory
is used only to prove triangle identities. Naturality is proved on the full
Hom categories, so odd morphisms are not discarded.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private theorem leftZigzag_explicit {C : Type u} [Bicategory.{w,v} C]
    {a b : C} {E : a ⟶ b} {F : b ⟶ a}
    (η : 𝟙 a ⟶ E ≫ F) (ε : F ≫ E ⟶ 𝟙 b) :
    Bicategory.leftZigzag η ε = Bicategory.whiskerRight η E ≫
      (Bicategory.associator E F E).hom ≫ Bicategory.whiskerLeft E ε := by
  unfold Bicategory.leftZigzag
  bicategory

private theorem rightZigzag_explicit {C : Type u} [Bicategory.{w,v} C]
    {a b : C} {E : a ⟶ b} {F : b ⟶ a}
    (η : 𝟙 a ⟶ E ≫ F) (ε : F ≫ E ⟶ 𝟙 b) :
    Bicategory.rightZigzag η ε = Bicategory.whiskerLeft F η ≫
      (Bicategory.associator F E F).inv ≫ Bicategory.whiskerRight ε F := by
  unfold Bicategory.rightZigzag
  bicategory

/-- Even adjunction data can be used by ordinary bicategorical coherence. -/
def SuperAdjunction.toUnderlying {b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) :
    Bicategory.Adjunction (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F) where
  unit := ⟨A.unit, A.unit_mem⟩
  counit := ⟨A.counit, A.counit_mem⟩
  left_triangle := by
    rw [leftZigzag_explicit]
    apply Subtype.ext
    change A.unit ▷ E ≫ (associator E F E).hom ≫ E ◁ A.counit =
      (leftUnitor E).hom ≫ (rightUnitor E).inv
    apply (cancel_epi (leftUnitor E).inv).mp
    apply (cancel_mono (rightUnitor E).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using A.left_triangle
  right_triangle := by
    rw [rightZigzag_explicit]
    apply Subtype.ext
    change F ◁ A.unit ≫ (associator F E F).inv ≫ A.counit ▷ F =
      (rightUnitor F).hom ≫ (leftUnitor F).inv
    apply (cancel_epi (rightUnitor F).inv).mp
    apply (cancel_mono (leftUnitor F).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using A.right_triangle

/-- Ordinary postcomposition, used only on the even underlying bicategory. -/
private def postYoneda {C : Type u} [Bicategory.{w,v} C] (a : C) : Pseudofunctor C Cat.{w,v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun b => Cat.of (a ⟶ b))
    (fun b c => Bicategory.postcomposingCat a b c)
  mapId b := Bicategory.rightUnitorNatIsoCat a b
  mapComp f g := (Bicategory.associatorNatIsoLeftCat a f g).symm
  map₂_whisker_left := by
    intro b c d f g h η
    ext x
    change a ⟶ b at x
    dsimp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors,
      Functor.toPrefunctor, Cat.Hom.isoMk, Functor.toCatHom, NatTrans.toCatHom₂,
      Bicategory.postcomposingCat,
      Bicategory.postcomposing, Bicategory.postcomp, Bicategory.associatorNatIsoLeftCat,
      Bicategory.rightUnitorNatIsoCat]
    bicategory
  map₂_whisker_right := by
    intro b c d f g η h
    ext x
    change a ⟶ b at x
    dsimp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors,
      Functor.toPrefunctor, Cat.Hom.isoMk, Functor.toCatHom, NatTrans.toCatHom₂,
      Bicategory.postcomposingCat,
      Bicategory.postcomposing, Bicategory.postcomp, Bicategory.associatorNatIsoLeftCat,
      Bicategory.rightUnitorNatIsoCat]
    bicategory
  map₂_associator := by
    intro b c d e f g h
    ext x
    change a ⟶ b at x
    dsimp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors,
      Functor.toPrefunctor, Cat.Hom.isoMk, Functor.toCatHom, NatTrans.toCatHom₂,
      Bicategory.postcomposingCat,
      Bicategory.postcomposing, Bicategory.postcomp, Bicategory.associatorNatIsoLeftCat,
      Bicategory.rightUnitorNatIsoCat]
    bicategory
  map₂_left_unitor := by
    intro b c f
    ext x
    change a ⟶ b at x
    dsimp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors,
      Functor.toPrefunctor, Cat.Hom.isoMk, Functor.toCatHom, NatTrans.toCatHom₂,
      Bicategory.postcomposingCat,
      Bicategory.postcomposing, Bicategory.postcomp, Bicategory.associatorNatIsoLeftCat,
      Bicategory.rightUnitorNatIsoCat]
    bicategory
  map₂_right_unitor := by
    intro b c f
    ext x
    change a ⟶ b at x
    dsimp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors,
      Functor.toPrefunctor, Cat.Hom.isoMk, Functor.toCatHom, NatTrans.toCatHom₂,
      Bicategory.postcomposingCat,
      Bicategory.postcomposing, Bicategory.postcomp, Bicategory.associatorNatIsoLeftCat,
      Bicategory.rightUnitorNatIsoCat]
    bicategory

/-- The postcomposition associator on full Hom categories. -/
def homPostComp {a b c d : B} (E : b ⟶ c) (F : c ⟶ d) :
    homPost (k := k) (a := a) E ⋙ homPost (k := k) F ≅ homPost (k := k) (E ≫ F) :=
  NatIso.ofComponents (fun f => associator f E F) (by
    intro f g η
    exact TwoSupercategory.associator_naturality_left (R := k) η E F)

/-- The postcomposition unitor on full Hom categories. -/
def homPostId (a b : B) : homPost (k := k) (a := a) (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (fun f => rightUnitor f) (by
    intro f g η
    exact TwoSupercategory.rightUnitor_naturality (R := k) η)

/-- The actual unit of the Hom-sector postcomposition adjunction. -/
def homPostUnit {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) :
    𝟭 (a ⟶ b) ⟶ homPost (k := k) E ⋙ homPost (k := k) F :=
  (homPostId a b).inv ≫ (homPostTransform A.unit A.unit_mem).toNatTrans ≫
    (homPostComp E F).inv

/-- The actual counit of the Hom-sector postcomposition adjunction. -/
def homPostCounit {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) :
    homPost (k := k) (a := a) F ⋙ homPost (k := k) E ⟶ 𝟭 (a ⟶ c) :=
  (homPostComp F E).hom ≫ (homPostTransform A.counit A.counit_mem).toNatTrans ≫
    (homPostId a c).hom

/-- Postcomposition preserves the right adjunction on full super Hom categories. -/
def homPostAdjunction {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) :
    homPost (k := k) (a := a) E ⊣ homPost (k := k) F where
  unit := homPostUnit A
  counit := homPostCounit A
  left_triangle_components f := by
    have h := (CategoryTheory.Adjunction.ofCat
      ((postYoneda (⟨a⟩ : Underlying2 k B)).mapAdjunction A.toUnderlying)).left_triangle_components
      (⟨f⟩ : Underlying k (a ⟶ b))
    exact congrArg Subtype.val h
  right_triangle_components f := by
    have h := (CategoryTheory.Adjunction.ofCat
      ((postYoneda (⟨a⟩ : Underlying2 k B)).mapAdjunction A.toUnderlying)).right_triangle_components
      (⟨f⟩ : Underlying k (a ⟶ c))
    exact congrArg Subtype.val h

private def reverseAdjunction {C : Type u} [Bicategory.{w,v} C]
    {a b : C} {E : a ⟶ b} {F : b ⟶ a} (A : Bicategory.Adjunction E F) :
    Bicategory.Adjunction F.op E.op where
  unit := Bicategory.Opposite.op2 A.unit
  counit := Bicategory.Opposite.op2 A.counit
  left_triangle := by
    rw [leftZigzag_explicit]
    have h := A.right_triangle
    rw [rightZigzag_explicit] at h
    exact congrArg Bicategory.Opposite.op2 h
  right_triangle := by
    rw [rightZigzag_explicit]
    have h := A.left_triangle
    rw [leftZigzag_explicit] at h
    exact congrArg Bicategory.Opposite.op2 h

/-- The precomposition associator on full Hom categories. -/
def homPreComp {a b c d : B} (E : a ⟶ b) (F : b ⟶ c) :
    homPre (k := k) (c := d) F ⋙ homPre (k := k) E ≅ homPre (k := k) (E ≫ F) :=
  (NatIso.ofComponents (fun f => associator E F f) (by
    intro f g η
    exact TwoSupercategory.associator_naturality_right (R := k) E F η)).symm

/-- The precomposition unitor on full Hom categories. -/
def homPreId (a b : B) : homPre (k := k) (c := b) (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (fun f => leftUnitor f) (by
    intro f g η
    exact TwoSupercategory.leftUnitor_naturality (R := k) η)

/-- The unit for reversed precomposition adjoints. -/
def homPreUnit {a b c : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) :
    𝟭 (a ⟶ c) ⟶ homPre (k := k) F ⋙ homPre (k := k) E :=
  (homPreId a c).inv ≫ (homPreTransform A.unit A.unit_mem).toNatTrans ≫
    (homPreComp E F).inv

/-- The counit for reversed precomposition adjoints. -/
def homPreCounit {a b c : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) :
    homPre (k := k) (c := c) E ⋙ homPre (k := k) F ⟶ 𝟭 (b ⟶ c) :=
  (homPreComp F E).hom ≫ (homPreTransform A.counit A.counit_mem).toNatTrans ≫
    (homPreId b c).hom

/-- Precomposition reverses adjoints, on full super Hom categories. -/
def homPreAdjunction {a b c : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) :
    homPre (k := k) (c := c) F ⊣ homPre (k := k) E where
  unit := homPreUnit A
  counit := homPreCounit A
  left_triangle_components f := by
    have h := (CategoryTheory.Adjunction.ofCat
      ((postYoneda (Opposite.op (⟨c⟩ : Underlying2 k B))).mapAdjunction
        (reverseAdjunction A.toUnderlying))).left_triangle_components
      (Underlying2.hom1 (R := k) f).op
    exact congrArg (fun z => z.unop2.val) h
  right_triangle_components f := by
    have h := (CategoryTheory.Adjunction.ofCat
      ((postYoneda (Opposite.op (⟨c⟩ : Underlying2 k B))).mapAdjunction
        (reverseAdjunction A.toUnderlying))).right_triangle_components
      (Underlying2.hom1 (R := k) f).op
    exact congrArg (fun z => z.unop2.val) h

/-- Both postcomposition adjunction maps are even on every Hom object. -/
theorem homPostUnit_mem {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (f : a ⟶ b) :
    (homPostUnit A).app f ∈ parity (R := k) _ _ 0 := by
  simpa [homPostUnit, homPostId, homPostComp, homPostTransform,
    SuperNatTrans.toNatTrans, homPre, homPost] using
    comp_mem (inv_mem (rightUnitor f) (TwoSupercategory.rightUnitor_hom_mem (R := k) f))
      (comp_mem (TwoSupercategory.whiskerLeft_mem f A.unit_mem)
        (inv_mem (associator f E F) (TwoSupercategory.associator_hom_mem (R := k) f E F)))

/-- The postcomposition counit has even components. -/
theorem homPostCounit_mem {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (f : a ⟶ c) :
    (homPostCounit A).app f ∈ parity (R := k) _ _ 0 := by
  simpa [homPostCounit, homPostId, homPostComp, homPostTransform,
    SuperNatTrans.toNatTrans, homPre, homPost] using
    comp_mem (TwoSupercategory.associator_hom_mem (R := k) f F E)
      (comp_mem (TwoSupercategory.whiskerLeft_mem f A.counit_mem)
        (TwoSupercategory.rightUnitor_hom_mem (R := k) f))

/-- The reversed precomposition unit has even components. -/
theorem homPreUnit_mem {a b c : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) (f : a ⟶ c) :
    (homPreUnit A).app f ∈ parity (R := k) _ _ 0 := by
  simpa [homPreUnit, homPreId, homPreComp, homPreTransform,
    SuperNatTrans.toNatTrans, homPre, homPost] using
    comp_mem (inv_mem (leftUnitor f) (TwoSupercategory.leftUnitor_hom_mem (R := k) f))
      (comp_mem (TwoSupercategory.whiskerRight_mem f A.unit_mem)
        (TwoSupercategory.associator_hom_mem (R := k) E F f))

/-- The reversed precomposition counit has even components. -/
theorem homPreCounit_mem {a b c : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) (f : b ⟶ c) :
    (homPreCounit A).app f ∈ parity (R := k) _ _ 0 := by
  simpa [homPreCounit, homPreId, homPreComp, homPreTransform,
    SuperNatTrans.toNatTrans, homPre, homPost] using
    comp_mem (inv_mem (associator F E f) (TwoSupercategory.associator_hom_mem (R := k) F E f))
      (comp_mem (TwoSupercategory.whiskerRight_mem f A.counit_mem)
        (TwoSupercategory.leftUnitor_hom_mem (R := k) f))

end OddMath.SKM

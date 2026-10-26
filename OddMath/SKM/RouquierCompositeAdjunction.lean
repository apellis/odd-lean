import OddMath.SKM.RouquierRightTranspose

/-!
# Composite even right adjunctions

The nested unit and counit used in `SignedFTriangle.md`, §2, are constructed
with both triangles derived. Only the even structural data pass through the
underlying bicategory; full-Hom right transposition remains available for odd maps.
Composition is in execution order, so the right adjoints reverse order.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private theorem underlying_left {C : Type u} [Bicategory.{w,v} C]
    {a b : C} {E : a ⟶ b} {F : b ⟶ a} (A : Bicategory.Adjunction E F) :
    (Bicategory.leftUnitor E).inv ≫ Bicategory.whiskerRight A.unit E ≫
      (Bicategory.associator E F E).hom ≫ Bicategory.whiskerLeft E A.counit ≫
      (Bicategory.rightUnitor E).hom = 𝟙 E := by
  calc
    _ = (Bicategory.leftUnitor E).inv ≫ Bicategory.leftZigzag A.unit A.counit ≫
      (Bicategory.rightUnitor E).hom := by unfold Bicategory.leftZigzag; bicategory
    _ = _ := by rw [A.left_triangle]; simp

private theorem underlying_right {C : Type u} [Bicategory.{w,v} C]
    {a b : C} {E : a ⟶ b} {F : b ⟶ a} (A : Bicategory.Adjunction E F) :
    (Bicategory.rightUnitor F).inv ≫ Bicategory.whiskerLeft F A.unit ≫
      (Bicategory.associator F E F).inv ≫ Bicategory.whiskerRight A.counit F ≫
      (Bicategory.leftUnitor F).hom = 𝟙 F := by
  calc
    _ = (Bicategory.rightUnitor F).inv ≫ Bicategory.rightZigzag A.unit A.counit ≫
      (Bicategory.leftUnitor F).hom := by unfold Bicategory.rightZigzag; bicategory
    _ = _ := by rw [A.right_triangle]; simp

private theorem comp_unit_formula {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : Bicategory.Adjunction E₁ F₁) (A₂ : Bicategory.Adjunction E₂ F₂) :
    (A₁.comp A₂).unit = A₁.unit ≫
      Bicategory.whiskerLeft E₁ (Bicategory.leftUnitor F₁).inv ≫
      Bicategory.whiskerLeft E₁ (Bicategory.whiskerRight A₂.unit F₁) ≫
      Bicategory.whiskerLeft E₁ (Bicategory.associator E₂ F₂ F₁).hom ≫
      (Bicategory.associator E₁ E₂ (F₂ ≫ F₁)).inv := by
  dsimp [Bicategory.Adjunction.comp, Bicategory.Adjunction.compUnit]
  bicategory

private theorem comp_counit_formula {C : Type u} [Bicategory.{w,v} C]
    {a b c : C} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : Bicategory.Adjunction E₁ F₁) (A₂ : Bicategory.Adjunction E₂ F₂) :
    (A₁.comp A₂).counit =
      (Bicategory.associator F₂ F₁ (E₁ ≫ E₂)).hom ≫
      Bicategory.whiskerLeft F₂ (Bicategory.associator F₁ E₁ E₂).inv ≫
      Bicategory.whiskerLeft F₂ (Bicategory.whiskerRight A₁.counit E₂) ≫
      Bicategory.whiskerLeft F₂ (Bicategory.leftUnitor E₂).hom ≫ A₂.counit := by
  dsimp [Bicategory.Adjunction.comp, Bicategory.Adjunction.compCounit]
  bicategory

namespace SuperAdjunction
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}

/-- Recover an even right adjunction from the even underlying bicategory. -/
def fromUnderlying {a b : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : Bicategory.Adjunction (Underlying2.hom1 (R := k) E)
      (Underlying2.hom1 (R := k) F)) : SuperAdjunction (k := k) E F where
  unit := A.unit.val
  counit := A.counit.val
  unit_mem := A.unit.property
  counit_mem := A.counit.property
  left_triangle := congrArg Subtype.val (underlying_left A)
  right_triangle := congrArg Subtype.val (underlying_right A)

/-- The actual composite right adjunction, with both snakes derived. -/
def comp (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    SuperAdjunction (k := k) (E₁ ≫ E₂) (F₂ ≫ F₁) :=
  fromUnderlying (A₁.toUnderlying.comp A₂.toUnderlying)

/-- The nested right units, with all associators in execution order. -/
theorem comp_unit (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    (A₁.comp A₂).unit = A₁.unit ≫ E₁ ◁ (leftUnitor F₁).inv ≫
      E₁ ◁ (A₂.unit ▷ F₁) ≫ E₁ ◁ (associator E₂ F₂ F₁).hom ≫
      (associator E₁ E₂ (F₂ ≫ F₁)).inv :=
  congrArg Subtype.val (comp_unit_formula A₁.toUnderlying A₂.toUnderlying)

/-- The nested right counits, without a left-adjunction hypothesis. -/
theorem comp_counit (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    (A₁.comp A₂).counit = (associator F₂ F₁ (E₁ ≫ E₂)).hom ≫
      F₂ ◁ (associator F₁ E₁ E₂).inv ≫ F₂ ◁ (A₁.counit ▷ E₂) ≫
      F₂ ◁ (leftUnitor E₂).hom ≫ A₂.counit :=
  congrArg Subtype.val (comp_counit_formula A₁.toUnderlying A₂.toUnderlying)

end SuperAdjunction
end OddMath.SKM

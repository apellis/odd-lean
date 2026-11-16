import OddMath.SKM.RouquierData
import StringDiagrams.Super.UnderlyingBicategory

/-!
# Horizontal opposition and reflected right adjunctions

The horizontal reflection in `SignedFTriangle.md` §3, supporting Brundan,
arXiv:1501.00350v1, Theorem 4.3. Objects are unchanged, 1-morphisms reverse,
and Hom supercategories (including all odd maps and vertical composition)
are unchanged. Whiskerings exchange sides; the associator is the inverse
on the reversed string, and unitors exchange. The reflected interchange
law uses the self-inverse Koszul sign, not ordinary interchange.

Mathlib's bicategorical opposite requires an ordinary bicategory on the
full Hom categories, so it cannot supply this construction.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

/-- The object type of the horizontal opposite 2-supercategory. -/
structure HOpS (B : Type u) where
  unop : B

namespace HOpS
variable {B : Type u} [BicategoryStruct.{w,v} B]

instance : BicategoryStruct.{w,v} (HOpS B) where
  Hom a b := b.unop ⟶ a.unop
  id a := 𝟙 a.unop
  comp f g := g ≫ f
  homCategory a b := inferInstanceAs (Category (b.unop ⟶ a.unop))
  whiskerLeft f _ _ η := η ▷ f
  whiskerRight η h := h ◁ η
  associator f g h := (associator h g f).symm
  leftUnitor f := rightUnitor f
  rightUnitor f := leftUnitor f

instance [∀ a b : B, Preadditive (a ⟶ b)] (a b : HOpS B) :
    Preadditive (a ⟶ b) := inferInstanceAs (Preadditive (b.unop ⟶ a.unop))

variable {k : Type r} [CommRing k]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]

instance (a b : HOpS B) : Linear k (a ⟶ b) :=
  inferInstanceAs (Linear k (b.unop ⟶ a.unop))
instance (a b : HOpS B) : Supercategory k (a ⟶ b) :=
  inferInstanceAs (Supercategory k (b.unop ⟶ a.unop))

variable [TwoSupercategory k B]

instance : TwoSupercategory k (HOpS B) where
  whiskerLeft_id f g := TwoSupercategory.id_whiskerRight (B := B) (R := k) g f
  whiskerLeft_comp f _ _ _ η θ := TwoSupercategory.comp_whiskerRight (B := B) (R := k) η θ f
  id_whiskerLeft η := TwoSupercategory.whiskerRight_id (B := B) (R := k) η
  comp_whiskerLeft f g _ _ η := TwoSupercategory.whiskerRight_comp (B := B) (R := k) η g f
  id_whiskerRight f g := TwoSupercategory.whiskerLeft_id (B := B) (R := k) g f
  comp_whiskerRight η θ i := TwoSupercategory.whiskerLeft_comp (B := B) (R := k) i η θ
  whiskerRight_id η := TwoSupercategory.id_whiskerLeft (B := B) (R := k) η
  whiskerRight_comp η g h := TwoSupercategory.comp_whiskerLeft (B := B) (R := k) h g η
  whisker_assoc f g g' η h := by
    change BicategoryStruct.whiskerLeft (B := B) h (BicategoryStruct.whiskerRight (B := B) η f) = (associator (B := B) h g f).inv ≫ BicategoryStruct.whiskerRight (B := B) (BicategoryStruct.whiskerLeft (B := B) h η) f ≫
      (associator (B := B) h g' f).hom
    rw [TwoSupercategory.whisker_assoc (B := B) (R := k)]
    simp
  pentagon f g h i := TwoSupercategory.pentagon_inv (B := B) k i h g f
  triangle f g := by
    change (associator (B := B) g (𝟙 _) f).inv ≫ BicategoryStruct.whiskerRight (B := B) (rightUnitor (B := B) g).hom f =
      BicategoryStruct.whiskerLeft (B := B) g (leftUnitor (B := B) f).hom
    rw [← TwoSupercategory.triangle (B := B) (R := k) g f]
    simp
  whiskerLeft_add f _ _ η θ := TwoSupercategory.add_whiskerRight (B := B) (R := k) η θ f
  add_whiskerRight η θ h := TwoSupercategory.whiskerLeft_add (B := B) (R := k) h η θ
  whiskerLeft_smul f _ _ r η := TwoSupercategory.smul_whiskerRight (B := B) r η f
  smul_whiskerRight r η h := TwoSupercategory.whiskerLeft_smul (B := B) h r η
  whiskerLeft_mem f _ _ _ _ hη := TwoSupercategory.whiskerRight_mem (B := B) f hη
  whiskerRight_mem h hη := TwoSupercategory.whiskerLeft_mem (B := B) h hη
  super_interchange {a b c} {f g} {h i} {p q} {η} {θ} hη hθ := by
    change BicategoryStruct.whiskerLeft (B := B) h η ≫
        BicategoryStruct.whiskerRight (B := B) θ g = koszulSign p q •
          (BicategoryStruct.whiskerRight (B := B) θ f ≫
            BicategoryStruct.whiskerLeft (B := B) i η)
    have h := TwoSupercategory.super_interchange (B := B) hθ hη
    rw [koszulSign_comm q p] at h
    simpa only [koszulSign_smul_smul] using
      (congrArg (fun z => koszulSign p q • z) h).symm
  associator_hom_mem f g h := inv_mem _ (TwoSupercategory.associator_hom_mem (B := B) (R := k) h g f)
  leftUnitor_hom_mem f := TwoSupercategory.rightUnitor_hom_mem (B := B) (R := k) f
  rightUnitor_hom_mem f := TwoSupercategory.leftUnitor_hom_mem (B := B) (R := k) f

end HOpS

namespace SuperAdjunction
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b : B} {E : a ⟶ b} {F : b ⟶ a}

/-- Horizontal reflection exchanges the adjoints, keeping the same unit and counit.
The two snake identities are exchanged, not assumed anew. -/
def horizontalOpposite (A : SuperAdjunction (k := k) E F) :
    SuperAdjunction (k := k) (B := HOpS B) (a := ⟨a⟩) (b := ⟨b⟩) F E where
  unit := A.unit
  counit := A.counit
  unit_mem := A.unit_mem
  counit_mem := A.counit_mem
  left_triangle := A.right_triangle
  right_triangle := A.left_triangle

end SuperAdjunction
end OddMath.SKM

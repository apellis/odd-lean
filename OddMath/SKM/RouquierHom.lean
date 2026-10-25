import OddMath.SKM.RouquierData

/-!
# Super Hom-sector functors

Ports the Hom-sector generators of `Categorification/TwoRep/RouqProduct.lean`
and the signed naturality needed by `Categorification/TwoRep/RouqProductKLR.lean`.
The functors act on the full super Hom categories, not only their even parts.
The interchange comparison is the associator, but odd transformations from
opposite sides obey super-interchange. These constructions alone do not fuse
colours and do not assert the Rouquier inversion of a coupled action.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- Postcomposition by a sector 1-morphism on the full Hom supercategory. -/
def homPost {a b c : B} (e : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := f ≫ e
  map η := η ▷ e
  map_id f := TwoSupercategory.id_whiskerRight (R := k) f e
  map_comp η θ := TwoSupercategory.comp_whiskerRight (R := k) η θ e

/-- Precomposition by the opposite sector. -/
def homPre {a b c : B} (e : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj f := e ≫ f
  map η := e ◁ η
  map_id f := TwoSupercategory.whiskerLeft_id (R := k) e f
  map_comp η θ := TwoSupercategory.whiskerLeft_comp (R := k) e η θ

instance {a b c : B} (e : b ⟶ c) : (homPost (k := k) (a := a) e).Additive where
  map_add {_ _} {f g} := TwoSupercategory.add_whiskerRight (R := k) f g e

instance {a b c : B} (e : a ⟶ b) : (homPre (k := k) (c := c) e).Additive where
  map_add {_ _} {f g} := TwoSupercategory.whiskerLeft_add (R := k) e f g

instance {a b c : B} (e : b ⟶ c) : (homPost (k := k) (a := a) e).Linear k where
  map_smul η r := TwoSupercategory.smul_whiskerRight r η e

instance {a b c : B} (e : a ⟶ b) : (homPre (k := k) (c := c) e).Linear k where
  map_smul η r := TwoSupercategory.whiskerLeft_smul e r η

instance {a b c : B} (e : b ⟶ c) : IsSuperfunctor k (homPost (k := k) (a := a) e) where
  map_mem h := TwoSupercategory.whiskerRight_mem e h

instance {a b c : B} (e : a ⟶ b) : IsSuperfunctor k (homPre (k := k) (c := c) e) where
  map_mem h := TwoSupercategory.whiskerLeft_mem e h

/-- The homogeneous postcomposition transformation, with its signed naturality. -/
def homPostTransform {a b c : B} {e e' : b ⟶ c} {p : ZMod 2}
    (η : e ⟶ e') (hη : η ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (homPost (k := k) (a := a) e) (homPost (k := k) e') where
  app q f := if q = p then f ◁ η else 0
  app_mem q f := by
    split_ifs with h
    · subst q; exact TwoSupercategory.whiskerLeft_mem f hη
    · exact Submodule.zero_mem _
  naturality q f g s θ hθ := by
    dsimp only [homPost]
    split_ifs with h
    · subst q
      simpa only [koszulSign_comm s p] using TwoSupercategory.super_interchange hθ hη
    · simp

/-- The homogeneous precomposition transformation, with its signed naturality. -/
def homPreTransform {a b c : B} {e e' : a ⟶ b} {p : ZMod 2}
    (η : e ⟶ e') (hη : η ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (homPre (k := k) (c := c) e) (homPre (k := k) e') where
  app q f := if q = p then η ▷ f else 0
  app_mem q f := by
    split_ifs with h
    · subst q; exact TwoSupercategory.whiskerRight_mem f hη
    · exact Submodule.zero_mem _
  naturality q f g s θ hθ := by
    dsimp only [homPre]
    split_ifs with h
    · subst q
      rw [TwoSupercategory.super_interchange hη hθ, koszulSign_smul_smul]
    · simp

/-- The two sector functors commute via the associator; no odd dot is made even. -/
def homSectorInterchange {a b c d : B} (e : a ⟶ b) (f : c ⟶ d) :
    homPre (k := k) (c := c) e ⋙ homPost (k := k) f ≅
      homPost (k := k) (a := b) f ⋙ homPre (k := k) e :=
  NatIso.ofComponents (fun g => associator e g f) (by
    intro g g' η
    change (e ◁ η) ▷ f ≫ (associator e g' f).hom =
      (associator e g f).hom ≫ e ◁ (η ▷ f)
    rw [TwoSupercategory.whisker_assoc (R := k)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The mixed exchange law used for opposite-sector homogeneous generators.
It replaces the unsigned `whisker_exchange` used in the even Hom product. -/
theorem homSector_exchange {a b c : B} {e e' : a ⟶ b} {f f' : b ⟶ c}
    {p q : ZMod 2} {η : e ⟶ e'} {θ : f ⟶ f'}
    (hη : η ∈ parity (R := k) _ _ p) (hθ : θ ∈ parity (R := k) _ _ q) :
    η ▷ f ≫ e' ◁ θ = koszulSign p q • (e ◁ θ ≫ η ▷ f') :=
  TwoSupercategory.super_interchange hη hθ

/-- Odd transformations from the two sides anticommute rather than commute. -/
example {a b c : B} {e e' : a ⟶ b} {f f' : b ⟶ c}
    {η : e ⟶ e'} {θ : f ⟶ f'}
    (hη : η ∈ parity (R := k) _ _ 1) (hθ : θ ∈ parity (R := k) _ _ 1) :
    η ▷ f ≫ e' ◁ θ = -(e ◁ θ ≫ η ▷ f') := by
  simpa using homSector_exchange hη hθ

end OddMath.SKM

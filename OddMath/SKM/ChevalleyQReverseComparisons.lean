/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTransport

/-!
# Comparison isomorphisms of the inverse of `ω_q`

The composition and identity comparisons of `G_q`, obtained by lifting the comparisons of `ω_q` through its fully faithful hom functors.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- The forward image of the proposed reverse composition comparison. -/
def chevalleyQReverseCompImage
    {a b c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : a ⟶ b) (g : b ⟶ c) :
    chevalleyQTwo.map ((chevalleyQReverseHom a b).obj f ≫
      (chevalleyQReverseHom b c).obj g) ≅
    chevalleyQTwo.map ((chevalleyQReverseHom a c).obj (f ≫ g)) :=
  (chevalleyQTwo.mapComp _ _).symm ≪≫
    TwoSupercategory.whiskerRightIso (R := k) (chevalleyQReverseHomCounit f)
      (chevalleyQTwo.map ((chevalleyQReverseHom b c).obj g)) ≪≫
    TwoSupercategory.whiskerLeftIso (R := k)
      (a := chevalleyQTwo.obj (chevalleyQReverseObj a))
      (b := chevalleyQTwo.obj (chevalleyQReverseObj b))
      (c := chevalleyQTwo.obj (chevalleyQReverseObj c))
      ((chevalleyQReverseTransport a b).obj f)
      (chevalleyQReverseHomCounit g) ≪≫
    (eqToIso (chevalleyQReverseTransport_comp f g)).symm ≪≫
    (chevalleyQReverseHomCounit (f ≫ g)).symm

/-- Reverse composition comparison, lifted through the forward hom map. -/
def chevalleyQReverseMapComp
    {a b c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : a ⟶ b) (g : b ⟶ c) :
    (chevalleyQReverseHom a b).obj f ≫ (chevalleyQReverseHom b c).obj g ≅
      (chevalleyQReverseHom a c).obj (f ≫ g) :=
  (chevQHom (negWeight a.unop.as)
    (negWeight c.unop.as)).preimageIso (chevalleyQReverseCompImage f g)

/-- The forward image of the proposed reverse identity comparison. -/
def chevalleyQReverseIdImage
    (a : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    chevalleyQTwo.map (𝟙 (chevalleyQReverseObj a)) ≅
      chevalleyQTwo.map ((chevalleyQReverseHom a a).obj (𝟙 a)) :=
  (chevalleyQTwo.mapId (chevalleyQReverseObj a)).symm ≪≫
    (eqToIso (chevalleyQReverseTransport_id a)).symm ≪≫
    (chevalleyQReverseHomCounit (𝟙 a)).symm

/-- Reverse identity comparison, lifted through the forward hom map. -/
def chevalleyQReverseMapId
    (a : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    𝟙 (chevalleyQReverseObj a) ≅ (chevalleyQReverseHom a a).obj (𝟙 a) :=
  (chevQHom (negWeight a.unop.as)
    (negWeight a.unop.as)).preimageIso (chevalleyQReverseIdImage a)

/-- The composition comparison has the specified forward image, on the functor. -/
theorem chevalleyQReverseMapComp_image
    {a b c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : a ⟶ b) (g : b ⟶ c) :
    chevalleyQTwo.map₂ (chevalleyQReverseMapComp f g).hom =
      (chevalleyQReverseCompImage f g).hom :=
  (chevQHom (negWeight a.unop.as)
    (negWeight c.unop.as)).map_preimage _

/-- The identity comparison has the specified forward image. -/
theorem chevalleyQReverseMapId_image
    (a : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    chevalleyQTwo.map₂ (chevalleyQReverseMapId a).hom = (chevalleyQReverseIdImage a).hom :=
  (chevQHom (negWeight a.unop.as)
    (negWeight a.unop.as)).map_preimage _

end OddMath.SKM

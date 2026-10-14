/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseComparisonGrading

/-!
# Naturality of endpoint transport

Naturality squares for the transported composition comparison of `G_q`.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- Left naturality of equality transport, on arbitrary morphisms. -/
theorem chevQEndpointTransport_comp_left
    {a b c a' b' c' : UGr D Sc sy hc} (p : a = a') (q : b = b') (r : c = c')
    {f f' : (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b⟩⟩}
    (η : f ⟶ f')
    (g : (⟨⟨b⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨c⟩⟩) :
    BicategoryStruct.whiskerRight
      (a := (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))))
      (b := ⟨⟨b'⟩⟩) (c := ⟨⟨c'⟩⟩)
      ((chevQEndpointTransport p q).map η) ((chevQEndpointTransport q r).obj g) ≫
      eqToHom (chevQEndpointTransport_comp p q r f' g).symm =
    eqToHom (chevQEndpointTransport_comp p q r f g).symm ≫
      (chevQEndpointTransport p r).map (η ▷ g) := by
  subst a' b' c'
  change η ▷ g ≫ 𝟙 (f' ≫ g) = 𝟙 (f ≫ g) ≫ η ▷ g
  rw [Category.comp_id, Category.id_comp]

/-- Left transport square at the double-negation endpoints. -/
theorem chevalleyQReverseTransport_comp_left
    {a b c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} {f f' : a ⟶ b}
    (η : f ⟶ f') (g : b ⟶ c) :
    BicategoryStruct.whiskerRight
      (a := chevalleyQTwo.obj (chevalleyQReverseObj a))
      (b := chevalleyQTwo.obj (chevalleyQReverseObj b))
      (c := chevalleyQTwo.obj (chevalleyQReverseObj c))
      ((chevalleyQReverseTransport a b).map η) ((chevalleyQReverseTransport b c).obj g) ≫
      eqToHom (chevalleyQReverseTransport_comp f' g).symm =
    eqToHom (chevalleyQReverseTransport_comp f g).symm ≫
      (chevalleyQReverseTransport a c).map (η ▷ g) :=
  chevQEndpointTransport_comp_left (chevQ_negWeight_square a.unop.as).symm
    (chevQ_negWeight_square b.unop.as).symm (chevQ_negWeight_square c.unop.as).symm η g
/-- Right naturality of equality transport, on arbitrary morphisms. -/
theorem chevQEndpointTransport_comp_right
    {a b c a' b' c' : UGr D Sc sy hc} (p : a = a') (q : b = b') (r : c = c')
    (f : (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b⟩⟩)
    {g g' : (⟨⟨b⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨c⟩⟩}
    (η : g ⟶ g') :
    BicategoryStruct.whiskerLeft
      (a := (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))))
      (b := ⟨⟨b'⟩⟩) (c := ⟨⟨c'⟩⟩)
      ((chevQEndpointTransport p q).obj f) ((chevQEndpointTransport q r).map η) ≫
      eqToHom (chevQEndpointTransport_comp p q r f g').symm =
    eqToHom (chevQEndpointTransport_comp p q r f g).symm ≫
      (chevQEndpointTransport p r).map (f ◁ η) := by
  subst a' b' c'
  change f ◁ η ≫ 𝟙 (f ≫ g') = 𝟙 (f ≫ g) ≫ f ◁ η
  rw [Category.comp_id, Category.id_comp]

/-- Right transport square at the double-negation endpoints. -/
theorem chevalleyQReverseTransport_comp_right
    {a b c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : a ⟶ b)
    {g g' : b ⟶ c} (η : g ⟶ g') :
    BicategoryStruct.whiskerLeft
      (a := chevalleyQTwo.obj (chevalleyQReverseObj a))
      (b := chevalleyQTwo.obj (chevalleyQReverseObj b))
      (c := chevalleyQTwo.obj (chevalleyQReverseObj c))
      ((chevalleyQReverseTransport a b).obj f) ((chevalleyQReverseTransport b c).map η) ≫
      eqToHom (chevalleyQReverseTransport_comp f g').symm =
    eqToHom (chevalleyQReverseTransport_comp f g).symm ≫
      (chevalleyQReverseTransport a c).map (f ◁ η) :=
  chevQEndpointTransport_comp_right (chevQ_negWeight_square a.unop.as).symm
    (chevQ_negWeight_square b.unop.as).symm (chevQ_negWeight_square c.unop.as).symm f η
end OddMath.SKM

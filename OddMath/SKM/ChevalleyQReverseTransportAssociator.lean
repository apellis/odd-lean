/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseComparisonUnits

/-!
# Associator coherence of endpoint transport

Compatibility of the transported comparisons with the associator.

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

/-- Equality transport satisfies the associator pasting identity. -/
theorem chevQEndpointTransport_associator
    {a b c d a' b' c' d' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (r : c = c') (s : d = d')
    (f : (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b⟩⟩)
    (g : (⟨⟨b⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨c⟩⟩)
    (h : (⟨⟨c⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨d⟩⟩) :
    let A : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)) := ⟨⟨a'⟩⟩
    let B : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)) := ⟨⟨b'⟩⟩
    let C : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)) := ⟨⟨c'⟩⟩
    let E : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)) := ⟨⟨d'⟩⟩
    let tf : A ⟶ B := (chevQEndpointTransport p q).obj f
    let tg : B ⟶ C := (chevQEndpointTransport q r).obj g
    let th : C ⟶ E := (chevQEndpointTransport r s).obj h
    tf ◁ eqToHom (chevQEndpointTransport_comp q r s g h).symm ≫
      eqToHom (chevQEndpointTransport_comp p q s f (g ≫ h)).symm ≫
      (chevQEndpointTransport p s).map (associator f g h).inv =
    (associator tf tg th).inv ≫
      eqToHom (chevQEndpointTransport_comp p q r f g).symm ▷ th ≫
      eqToHom (chevQEndpointTransport_comp p r s (f ≫ g) h).symm := by
  subst a' b' c' d'
  change f ◁ 𝟙 (g ≫ h) ≫ 𝟙 _ ≫ (associator f g h).inv =
    (associator f g h).inv ≫ 𝟙 (f ≫ g) ▷ h ≫ 𝟙 _
  rw [whiskerLeft_id (R := k), id_whiskerRight (R := k), Category.id_comp,
    Category.id_comp, Category.id_comp, Category.comp_id]
end OddMath.SKM

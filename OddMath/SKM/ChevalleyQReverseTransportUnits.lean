/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseComparisonNaturality

/-!
# Unit coherence of endpoint transport

Compatibility of the transported comparisons with the unitors.

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

/-- Left unit pasting for equality transport. -/
theorem chevQEndpointTransport_leftUnitor
    {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b⟩⟩) :
    BicategoryStruct.whiskerRight
      (a := (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))))
      (b := ⟨⟨a'⟩⟩) (c := ⟨⟨b'⟩⟩)
      (eqToHom (chevQEndpointTransport_id p).symm) ((chevQEndpointTransport p q).obj f) ≫
      eqToHom (chevQEndpointTransport_comp p p q (𝟙 _) f).symm ≫
      (chevQEndpointTransport p q).map (leftUnitor f).hom =
    (leftUnitor (show (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b'⟩⟩
      from (chevQEndpointTransport p q).obj f)).hom := by
  subst a' b'
  change (𝟙 (𝟙 _)) ▷ f ≫ 𝟙 _ ≫ (leftUnitor f).hom = (leftUnitor f).hom
  rw [id_whiskerRight (R := k), Category.id_comp, Category.id_comp]

/-- Right unit pasting for equality transport. -/
theorem chevQEndpointTransport_rightUnitor
    {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b⟩⟩) :
    BicategoryStruct.whiskerLeft
      (a := (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))))
      (b := ⟨⟨b'⟩⟩) (c := ⟨⟨b'⟩⟩)
      ((chevQEndpointTransport p q).obj f) (eqToHom (chevQEndpointTransport_id q).symm) ≫
      eqToHom (chevQEndpointTransport_comp p q q f (𝟙 _)).symm ≫
      (chevQEndpointTransport p q).map (rightUnitor f).hom =
    (rightUnitor (show (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b'⟩⟩
      from (chevQEndpointTransport p q).obj f)).hom := by
  subst a' b'
  change f ◁ (𝟙 (𝟙 _)) ≫ 𝟙 _ ≫ (rightUnitor f).hom = (rightUnitor f).hom
  rw [whiskerLeft_id (R := k), Category.id_comp, Category.id_comp]
end OddMath.SKM

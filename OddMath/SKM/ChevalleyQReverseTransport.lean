/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseLinear

/-!
# Endpoint transport for the inverse of `ω_q`

Transport of hom categories along the equalities `-(-λ) = λ`, used to state the composition and identity comparisons of `G_q`.

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

/-- Endpoint equality transport preserves horizontal composition of Q arrows. -/
theorem chevQEndpointTransport_comp
    {a b c a' b' c' : UGr D Sc sy hc} (p : a = a') (q : b = b') (r : c = c')
    (f : (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b⟩⟩)
    (g : (⟨⟨b⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨c⟩⟩) :
    (chevQEndpointTransport p r).obj (f ≫ g) =
      (show (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨b'⟩⟩ from
        (chevQEndpointTransport p q).obj f) ≫
      (show (⟨⟨b'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) ⟶ ⟨⟨c'⟩⟩ from
        (chevQEndpointTransport q r).obj g) := by
  subst a' b' c'
  rfl

/-- Endpoint equality transport preserves the Q identity arrow. -/
theorem chevQEndpointTransport_id {a a' : UGr D Sc sy hc} (p : a = a') :
    (chevQEndpointTransport (k := k) p p).obj
      (𝟙 (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)))) =
      𝟙 (⟨⟨a'⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) := by
  subst a'
  rfl

/-- The reverse transport respects the three target endpoints. -/
theorem chevalleyQReverseTransport_comp
    {a b c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : a ⟶ b) (g : b ⟶ c) :
    (chevalleyQReverseTransport a c).obj (f ≫ g) =
      (show chevalleyQTwo.obj (chevalleyQReverseObj a) ⟶
        chevalleyQTwo.obj (chevalleyQReverseObj b) from
        (chevalleyQReverseTransport a b).obj f) ≫
      (show chevalleyQTwo.obj (chevalleyQReverseObj b) ⟶
        chevalleyQTwo.obj (chevalleyQReverseObj c) from
        (chevalleyQReverseTransport b c).obj g) :=
  chevQEndpointTransport_comp (chevQ_negWeight_square a.unop.as).symm
    (chevQ_negWeight_square b.unop.as).symm (chevQ_negWeight_square c.unop.as).symm f g

/-- The reverse transport respects the target identity. -/
theorem chevalleyQReverseTransport_id
    (a : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    (chevalleyQReverseTransport a a).obj (𝟙 a) =
      𝟙 (chevalleyQTwo.obj (chevalleyQReverseObj a)) :=
  chevQEndpointTransport_id (chevQ_negWeight_square a.unop.as).symm

end OddMath.SKM

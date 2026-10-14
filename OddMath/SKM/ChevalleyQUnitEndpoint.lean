/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQCounitCancel

/-!
# Endpoint transport and the hom counit for the unit of `ω_q`

Transport of 1-morphisms along weight equalities, and the counit `qUnitHomCounit` of the hom equivalence of `ω_q`, from which the unit components are built.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
  BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (F) (G)
local notation "O" a:max => (⟨a⟩ : QTwoEnvelope k (UGr D Sc sy hc))

def qUnitTransport {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b') :
    (O a ⟶ O b) ⥤ (O a' ⟶ O b') := by
  subst a' b'
  exact 𝟭 _

theorem qUnitTransport_comp {a b c a' b' c' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (r : c = c') (f : O a ⟶ O b) (g : O b ⟶ O c) :
    (qUnitTransport p r).obj (f ≫ g) =
      (qUnitTransport p q).obj f ≫ (qUnitTransport q r).obj g := by
  subst a' b' c'
  rfl

theorem qUnitTransport_id {a a' : UGr D Sc sy hc} (p : a = a') :
    (qUnitTransport p p).obj (𝟙 (O a)) = 𝟙 (O a') := by
  subst a'
  rfl

theorem qUnitTransport_forward {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (f : O a ⟶ O b) :
    (F).map ((qUnitTransport p q).obj f) =
      (chevQEndpointTransport (congrArg negWeight p) (congrArg negWeight q)).obj ((F).map f) := by
  subst a' b'
  rfl

theorem qUnitTransport_forward_map {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') {f g : O a ⟶ O b} (η : f ⟶ g) :
    (F).map₂ ((qUnitTransport p q).map η) ≫ eqToHom (qUnitTransport_forward p q g) =
      eqToHom (qUnitTransport_forward p q f) ≫
        (chevQEndpointTransport (congrArg negWeight p)
          (congrArg negWeight q)).map ((F).map₂ η) := by
  subst a' b'
  change (F).map₂ η ≫ 𝟙 _ = 𝟙 _ ≫ (F).map₂ η
  rw [Category.comp_id, Category.id_comp]

def qUnitHomTransport (a b : A) : (a ⟶ b) ⥤ ((H).obj a ⟶ (H).obj b) :=
  qUnitTransport (chevQ_negWeight_square a.as).symm (chevQ_negWeight_square b.as).symm

def qUnitHomCounit {a b : A} (f : a ⟶ b) :
    (H).map f ≅ (qUnitHomTransport a b).obj f :=
  (chevQHom (negWeight (negWeight a.as)) (negWeight (negWeight b.as))).preimageIso
    (chevalleyQReverseHomCounit ((F).map f) ≪≫
      (eqToIso (qUnitTransport_forward (chevQ_negWeight_square a.as).symm
        (chevQ_negWeight_square b.as).symm f)).symm)

theorem qUnitHomCounit_image {a b : A} (f : a ⟶ b) :
    (F).map₂ (qUnitHomCounit f).hom = (chevalleyQReverseHomCounit ((F).map f)).hom ≫
      eqToHom (qUnitTransport_forward (chevQ_negWeight_square a.as).symm
        (chevQ_negWeight_square b.as).symm f).symm := by
  exact (chevQHom (negWeight (negWeight a.as))
    (negWeight (negWeight b.as))).map_preimage _
end OddMath.SKM

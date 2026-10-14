/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitCoherence

/-!
# Reflection with weight transport

The reflection equations of `ChevalleyQUnitCoherence` along weight equalities.

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
local notation "B" => TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (F) (G)
local notation "O" a:max => (⟨a⟩ : QTwoEnvelope k (UGr D Sc sy hc))
local notation "T" p:max q:max =>
  chevQEndpointTransport (congrArg negWeight p) (congrArg negWeight q)

theorem qUnitReflect_comp {a b c a' b' c' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (r : c = c') : ∀
    (f : O a ⟶ O b) (g : O b ⟶ O c)
    (s : O a' ⟶ O b') (t : O b' ⟶ O c') (z : O a' ⟶ O c')
    (e : s ≅ (qUnitTransport p q).obj f)
    (e' : t ≅ (qUnitTransport q r).obj g)
    (e'' : z ≅ (qUnitTransport p r).obj (f ≫ g)) (κ : s ≫ t ⟶ z)
    (ε : (F).map s ⟶ (T p q).obj ((F).map f))
    (ε' : (F).map t ⟶ (T q r).obj ((F).map g))
    (ε'' : (F).map z ⟶ (T p r).obj ((F).map (f ≫ g)))
    (_ : (F).map₂ e.hom = ε ≫ eqToHom (qUnitTransport_forward p q f).symm)
    (_ : (F).map₂ e'.hom = ε' ≫ eqToHom (qUnitTransport_forward q r g).symm)
    (_ : (F).map₂ e''.hom = ε'' ≫
      eqToHom (qUnitTransport_forward p r (f ≫ g)).symm)
    (_ : ((F).mapComp s t).hom ≫ (F).map₂ κ ≫ ε'' =
      ε ▷ (F).map t ≫
      (show (F).obj (O a') ⟶ (F).obj (O b') from (T p q).obj ((F).map f)) ◁ ε' ≫
      eqToHom (chevQEndpointTransport_comp
        (congrArg negWeight p) (congrArg negWeight q) (congrArg negWeight r)
        ((F).map f) ((F).map g)).symm ≫ (T p r).map ((F).mapComp f g).hom),
    κ ≫ e''.hom = e.hom ▷ t ≫
      (show O a' ⟶ O b' from (qUnitTransport p q).obj f) ◁ e'.hom ≫
      eqToHom (qUnitTransport_comp p q r f g).symm := by
  subst a' b' c'
  intro f g s t z e e' e'' κ ε ε' ε'' he he' he'' h
  exact qUnitReflect_comp_base f g s t z e e' e'' κ ε ε' ε'' he he' he'' h

theorem qUnitReflect_id {a a' : UGr D Sc sy hc} (p : a = a') : ∀
    (s : O a' ⟶ O a') (e : s ≅ (qUnitTransport p p).obj (𝟙 (O a)))
    (κ : 𝟙 (O a') ⟶ s)
    (ε : (F).map s ⟶ (T p p).obj ((F).map (𝟙 (O a))))
    (_ : (F).map₂ e.hom = ε ≫ eqToHom (qUnitTransport_forward p p (𝟙 (O a))).symm)
    (_ : ((F).mapId (O a')).hom ≫ (F).map₂ κ ≫ ε =
      eqToHom (chevQEndpointTransport_id (congrArg negWeight p)).symm ≫
        (T p p).map ((F).mapId (O a)).hom),
    κ ≫ e.hom = eqToHom (qUnitTransport_id p).symm := by
  subst a'
  intro s e κ ε he h
  exact qUnitReflect_id_base (O a) s e κ ε he h
end OddMath.SKM

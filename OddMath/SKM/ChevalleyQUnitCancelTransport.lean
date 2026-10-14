/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitInv

/-!
# Transport for the unit cancellations

Envelope unitor cancellation for the unit and its inverse.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
  BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "O" a:max => (⟨a⟩ : QTwoEnvelope k (UGr D Sc sy hc))

theorem qUnitPaddedCancel {a b : A} {s t : a ⟶ b} (e : s ≅ t) :
    ((associator s (𝟙 b) (𝟙 b)).inv ≫
      ((rightUnitor s).hom ≫ e.hom ≫ (leftUnitor t).inv) ▷ 𝟙 b ≫
      (associator (𝟙 a) t (𝟙 b)).hom ≫
      𝟙 a ◁ ((rightUnitor t).hom ≫ e.inv ≫ (leftUnitor s).inv) ≫
      (associator (𝟙 a) (𝟙 a) s).inv) ≫ (leftUnitor (𝟙 a)).hom ▷ s =
    s ◁ (leftUnitor (𝟙 b)).hom ≫ (rightUnitor s).hom ≫ (leftUnitor s).inv := by
  have nat : e.hom ▷ 𝟙 b ≫ (leftUnitor t).inv ▷ 𝟙 b ≫
      (associator (𝟙 a) t (𝟙 b)).hom ≫ 𝟙 a ◁ (rightUnitor t).hom =
      (leftUnitor s).inv ▷ 𝟙 b ≫ (associator (𝟙 a) s (𝟙 b)).hom ≫
      𝟙 a ◁ (rightUnitor s).hom ≫ 𝟙 a ◁ e.hom := by
    rw [← Category.assoc, ← comp_whiskerRight (R := k), leftUnitor_inv_naturality k,
      comp_whiskerRight (R := k), Category.assoc, associator_naturality_middle_assoc k,
      ← whiskerLeft_comp (R := k), rightUnitor_naturality k, whiskerLeft_comp (R := k)]
  simp only [comp_whiskerRight (R := k), whiskerLeft_comp (R := k), Category.assoc]
  rw [reassoc_of% nat, whiskerLeft_hom_inv_assoc k]
  have h : ((associator s (𝟙 b) (𝟙 b)).inv ≫
      ((rightUnitor s).hom ≫ (leftUnitor s).inv) ▷ 𝟙 b ≫
      (associator (𝟙 a) s (𝟙 b)).hom ≫
      𝟙 a ◁ ((rightUnitor s).hom ≫ (leftUnitor s).inv) ≫
      (associator (𝟙 a) (𝟙 a) s).inv) ≫ (leftUnitor (𝟙 a)).hom ▷ s =
      s ◁ (leftUnitor (𝟙 b)).hom ≫ (rightUnitor s).hom ≫ (leftUnitor s).inv :=
    (TwoNatTrans.leftUnitor (TwoNatTrans.id (TwoSuperfunctor.id k A))).hom.naturality s
  simpa only [comp_whiskerRight (R := k), whiskerLeft_comp (R := k), Category.assoc] using h

def qUnitInvCancel {a a' : UGr D Sc sy hc} (p : a = a') :
    qUnitInvObj p ≫ qUnitObj p ≅ 𝟙 (O a') := by
  subst a'
  exact leftUnitor (𝟙 _)

def qUnitCancel {a a' : UGr D Sc sy hc} (p : a = a') :
    qUnitObj p ≫ qUnitInvObj p ≅ 𝟙 (O a) := by
  subst a'
  exact leftUnitor (𝟙 _)

theorem qUnitInvCancel_naturality {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f) :
    ((associator s (qUnitInvObj q) (qUnitObj q)).inv ≫
      (qUnitInvCell p q f s e).hom ▷ qUnitObj q ≫
      (associator (qUnitInvObj p) f (qUnitObj q)).hom ≫
      qUnitInvObj p ◁ (qUnitCell p q f s e).hom ≫
      (associator (qUnitInvObj p) (qUnitObj p) s).inv) ≫ (qUnitInvCancel p).hom ▷ s =
    s ◁ (qUnitInvCancel q).hom ≫ (rightUnitor s).hom ≫ (leftUnitor s).inv := by
  subst a' b'
  change s ≅ f at e
  exact qUnitPaddedCancel e

theorem qUnitCancel_naturality {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f) :
    ((associator f (qUnitObj q) (qUnitInvObj q)).inv ≫
      (qUnitCell p q f s e).hom ▷ qUnitInvObj q ≫
      (associator (qUnitObj p) s (qUnitInvObj q)).hom ≫
      qUnitObj p ◁ (qUnitInvCell p q f s e).hom ≫
      (associator (qUnitObj p) (qUnitInvObj p) f).inv) ≫ (qUnitCancel p).hom ▷ f =
    f ◁ (qUnitCancel q).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv := by
  subst a' b'
  change s ≅ f at e
  exact qUnitPaddedCancel e.symm

theorem qUnitInvCancel_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qUnitInvCancel p).hom ∈ parity (R := k) _ _ 0 ∧
      (qUnitInvCancel p).hom ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨leftUnitor_hom_mem (R := k) _,
    GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := k) _⟩

theorem qUnitCancel_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qUnitCancel p).hom ∈ parity (R := k) _ _ 0 ∧
      (qUnitCancel p).hom ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨leftUnitor_hom_mem (R := k) _,
    GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := k) _⟩

theorem qUnitInvCancel_inv_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qUnitInvCancel p).inv ∈ parity (R := k) _ _ 0 ∧
      (qUnitInvCancel p).inv ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨inv_mem (C := O a ⟶ O a) (leftUnitor (𝟙 (O a)))
    (leftUnitor_hom_mem (R := k) _),
    GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := k) _⟩

theorem qUnitCancel_inv_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qUnitCancel p).inv ∈ parity (R := k) _ _ 0 ∧
      (qUnitCancel p).inv ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨inv_mem (C := O a ⟶ O a) (leftUnitor (𝟙 (O a)))
    (leftUnitor_hom_mem (R := k) _),
    GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := k) _⟩
end OddMath.SKM

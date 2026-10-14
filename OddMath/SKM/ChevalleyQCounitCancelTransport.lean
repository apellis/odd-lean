/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQCounitInv

/-!
# Transport for the counit cancellations

Unitor and endpoint transport for the two cancellation modifications of the counit and its inverse.

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
local notation "B" => TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))
local notation "O" a:max => (⟨⟨a⟩⟩ : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc)))

/-- Unitor cancellation for the two padded inverse hom components. -/
theorem qPaddedCancel {a b : B} {s t : a ⟶ b} (e : s ≅ t) :
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
    (TwoNatTrans.leftUnitor (TwoNatTrans.id (TwoSuperfunctor.id k B))).hom.naturality s
  simpa only [comp_whiskerRight (R := k), whiskerLeft_comp (R := k), Category.assoc] using h

def qCounitCancel {a a' : UGr D Sc sy hc} (p : a = a') :
    qCounitObj p ≫ qCounitInvObj p ≅ 𝟙 (O a') := by
  subst a'
  exact leftUnitor (𝟙 _)

def qCounitInvCancel {a a' : UGr D Sc sy hc} (p : a = a') :
    qCounitInvObj p ≫ qCounitObj p ≅ 𝟙 (O a) := by
  subst a'
  exact leftUnitor (𝟙 _)

theorem qCounitCancel_naturality {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (chevQEndpointTransport p q).obj f) :
    ((associator s (qCounitObj q) (qCounitInvObj q)).inv ≫
      (qCounitCell p q f s e).hom ▷ qCounitInvObj q ≫
      (associator (qCounitObj p) f (qCounitInvObj q)).hom ≫
      qCounitObj p ◁ (qCounitInvCell p q f s e).hom ≫
      (associator (qCounitObj p) (qCounitInvObj p) s).inv) ≫ (qCounitCancel p).hom ▷ s =
    s ◁ (qCounitCancel q).hom ≫ (rightUnitor s).hom ≫ (leftUnitor s).inv := by
  subst a' b'
  change s ≅ f at e
  exact qPaddedCancel e

theorem qCounitInvCancel_naturality {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (chevQEndpointTransport p q).obj f) :
    ((associator f (qCounitInvObj q) (qCounitObj q)).inv ≫
      (qCounitInvCell p q f s e).hom ▷ qCounitObj q ≫
      (associator (qCounitInvObj p) s (qCounitObj q)).hom ≫
      qCounitInvObj p ◁ (qCounitCell p q f s e).hom ≫
      (associator (qCounitInvObj p) (qCounitObj p) f).inv) ≫ (qCounitInvCancel p).hom ▷ f =
    f ◁ (qCounitInvCancel q).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv := by
  subst a' b'
  change s ≅ f at e
  exact qPaddedCancel e.symm

theorem qCounitCancel_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qCounitCancel p).hom ∈ parity (R := k) _ _ 0 ∧
      (qCounitCancel p).hom ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨leftUnitor_hom_mem (R := k) _,
    GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := k) _⟩

theorem qCounitInvCancel_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qCounitInvCancel p).hom ∈ parity (R := k) _ _ 0 ∧
      (qCounitInvCancel p).hom ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨leftUnitor_hom_mem (R := k) _,
    GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := k) _⟩
theorem qCounitCancel_inv_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qCounitCancel p).inv ∈ parity (R := k) _ _ 0 ∧
      (qCounitCancel p).inv ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨inv_mem (C := O a ⟶ O a) (leftUnitor (𝟙 (O a)))
    (leftUnitor_hom_mem (R := k) _),
    GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := k) _⟩

theorem qCounitInvCancel_inv_homogeneous {a a' : UGr D Sc sy hc} (p : a = a') :
    (qCounitInvCancel p).inv ∈ parity (R := k) _ _ 0 ∧
      (qCounitInvCancel p).inv ∈ degree (R := k) _ _ 0 := by
  subst a'
  exact ⟨inv_mem (C := O a ⟶ O a) (leftUnitor (𝟙 (O a)))
    (leftUnitor_hom_mem (R := k) _),
    GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := k) _⟩
end OddMath.SKM

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnit

/-!
# Transport for the inverse unit of `ω_q`

Endpoint pasting used to define the inverse unit `ω_q ⋙ G_q ⟹ 1`.

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
local notation "O" a:max => (⟨a⟩ : QTwoEnvelope k (UGr D Sc sy hc))

def qUnitInvObj {a a' : UGr D Sc sy hc} (p : a = a') : O a' ⟶ O a := by
  subst a'
  exact 𝟙 _

def qUnitInvCell {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f) :
    s ≫ qUnitInvObj q ≅ qUnitInvObj p ≫ f := by
  subst a' b'
  exact rightUnitor s ≪≫ e ≪≫ (leftUnitor f).symm

theorem qUnitInvCell_even {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (qUnitInvCell p q f s e).hom ∈ parity (R := k) _ _ 0 := by
  subst a' b'
  change s ≅ f at e
  change e.hom ∈ parity (R := k) (C := O a ⟶ O b) s f 0 at he
  change (rightUnitor s).hom ≫ e.hom ≫ (leftUnitor f).inv ∈
    parity (R := k) (C := O a ⟶ O b) (s ≫ 𝟙 (O b)) (𝟙 (O a) ≫ f) 0
  simpa only [add_zero] using
    comp_mem (C := O a ⟶ O b) (rightUnitor_hom_mem (R := k) s)
      (comp_mem (C := O a ⟶ O b) he
        (inv_mem (C := O a ⟶ O b) (leftUnitor f) (leftUnitor_hom_mem (R := k) f)))

theorem qUnitInvCell_degree {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f)
    (he : e.hom ∈ degree (R := k) _ _ 0) :
    (qUnitInvCell p q f s e).hom ∈ degree (R := k) _ _ 0 := by
  subst a' b'
  change s ≅ f at e
  change e.hom ∈ degree (R := k) (C := O a ⟶ O b) s f 0 at he
  change (rightUnitor s).hom ≫ e.hom ≫ (leftUnitor f).inv ∈
    degree (R := k) (C := O a ⟶ O b) (s ≫ 𝟙 (O b)) (𝟙 (O a) ≫ f) 0
  simpa only [add_zero] using
    comp_mem_degree (C := O a ⟶ O b)
      (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := k) s)
      (comp_mem_degree (C := O a ⟶ O b) he
        (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := k) f))

theorem qUnitInvCell_naturality {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    {f g : O a ⟶ O b} {s t : O a' ⟶ O b'}
    (e : s ≅ (qUnitTransport p q).obj f)
    (e' : t ≅ (qUnitTransport p q).obj g)
    (η : f ⟶ g) (θ : s ⟶ t)
    (h : θ ≫ e'.hom = e.hom ≫ (qUnitTransport p q).map η) :
    θ ▷ qUnitInvObj q ≫ (qUnitInvCell p q g t e').hom =
      (qUnitInvCell p q f s e).hom ≫ qUnitInvObj p ◁ η := by
  subst a' b'
  change s ≅ f at e
  change t ≅ g at e'
  change θ ≫ e'.hom = e.hom ≫ η at h
  change θ ▷ 𝟙 _ ≫ (rightUnitor t).hom ≫ e'.hom ≫ (leftUnitor g).inv =
    ((rightUnitor s).hom ≫ e.hom ≫ (leftUnitor f).inv) ≫ 𝟙 _ ◁ η
  rw [rightUnitor_naturality_assoc k, reassoc_of% h, leftUnitor_inv_naturality k]
  simp only [Category.assoc]

theorem qUnitInvCell_comp {a b c a' b' c' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (r : c = c')
    (f : O a ⟶ O b) (g : O b ⟶ O c)
    (s : O a' ⟶ O b') (t : O b' ⟶ O c') (z : O a' ⟶ O c')
    (e : s ≅ (qUnitTransport p q).obj f)
    (e' : t ≅ (qUnitTransport q r).obj g)
    (e'' : z ≅ (qUnitTransport p r).obj (f ≫ g))
    (κ : s ≫ t ⟶ z) (he : e.hom ∈ parity (R := k) _ _ 0)
    (h : κ ≫ e''.hom = e.hom ▷ t ≫
      (show O a' ⟶ O b' from (qUnitTransport p q).obj f) ◁ e'.hom ≫
      eqToHom (qUnitTransport_comp p q r f g).symm) :
    κ ▷ qUnitInvObj r ≫ (qUnitInvCell p r (f ≫ g) z e'').hom =
      (associator s t (qUnitInvObj r)).hom ≫ s ◁ (qUnitInvCell q r g t e').hom ≫
      (associator s (qUnitInvObj q) g).inv ≫ (qUnitInvCell p q f s e).hom ▷ g ≫
      (associator (qUnitInvObj p) f g).hom ≫ qUnitInvObj p ◁ 𝟙 (f ≫ g) := by
  subst a' b' c'
  change s ≅ f at e
  change t ≅ g at e'
  change z ≅ f ≫ g at e''
  change e.hom ∈ parity (R := k) (C := O a ⟶ O b) s f 0 at he
  change κ ≫ e''.hom = e.hom ▷ t ≫ f ◁ e'.hom ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  change κ ▷ 𝟙 _ ≫ (rightUnitor z).hom ≫ e''.hom ≫ (leftUnitor (f ≫ g)).inv =
    (associator s t (𝟙 _)).hom ≫ s ◁ ((rightUnitor t).hom ≫ e'.hom ≫ (leftUnitor g).inv) ≫
      (associator s (𝟙 _) g).inv ≫ ((rightUnitor s).hom ≫ e.hom ≫ (leftUnitor f).inv) ▷ g ≫
      (associator (𝟙 _) f g).hom ≫ 𝟙 _ ◁ 𝟙 (f ≫ g)
  have tri : (associator s (𝟙 _) g).inv ≫ (rightUnitor s).hom ▷ g =
      s ◁ (leftUnitor g).hom := by
    rw [← TwoSupercategory.triangle (R := k), Iso.inv_hom_id_assoc]
  rw [rightUnitor_naturality_assoc k, reassoc_of% h]
  simp only [whiskerLeft_comp' k, comp_whiskerRight' k, whiskerLeft_id (R := k),
    Category.comp_id, Category.assoc]
  rw [reassoc_of% tri, whiskerLeft_inv_hom_assoc k]
  rw [← leftUnitor_comp_inv k f g]
  rw [← Category.assoc (associator s t (𝟙 _)).hom, ← rightUnitor_comp k s t]
  rw [whisker_exchange_of_even_left_assoc he]

theorem qUnitInvCell_id {a a' : UGr D Sc sy hc} (p : a = a')
    (s : O a' ⟶ O a') (e : s ≅ (qUnitTransport p p).obj (𝟙 (O a)))
    (κ : 𝟙 (O a') ⟶ s)
    (h : κ ≫ e.hom = eqToHom (qUnitTransport_id p).symm) :
    (rightUnitor (qUnitInvObj p)).hom ≫ (leftUnitor (qUnitInvObj p)).inv ≫
      κ ▷ qUnitInvObj p ≫ (qUnitInvCell p p (𝟙 (O a)) s e).hom =
      qUnitInvObj p ◁ 𝟙 (𝟙 (O a)) := by
  subst a'
  change s ≅ 𝟙 (O a) at e
  change κ ≫ e.hom = 𝟙 (𝟙 (O a)) at h
  change (rightUnitor (𝟙 (O a))).hom ≫ (leftUnitor (𝟙 (O a))).inv ≫
    κ ▷ 𝟙 (O a) ≫ (rightUnitor s).hom ≫ e.hom ≫ (leftUnitor (𝟙 (O a))).inv =
      𝟙 (O a) ◁ 𝟙 (𝟙 (O a))
  rw [rightUnitor_naturality_assoc k, reassoc_of% h]
  simp only [unitors_inv_equal k, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    whiskerLeft_id (R := k)]
end OddMath.SKM

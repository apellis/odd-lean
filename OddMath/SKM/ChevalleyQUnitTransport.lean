/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitComparisons

/-!
# Components of the unit of `ω_q`

Object components and naturality cells of the unit, with their grading, naturality, and compatibility with composition and identities.

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

def qUnitObj {a a' : UGr D Sc sy hc} (p : a = a') : O a ⟶ O a' := by
  subst a'
  exact 𝟙 _

def qUnitCell {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f) :
    f ≫ qUnitObj q ≅ qUnitObj p ≫ s := by
  subst a' b'
  exact rightUnitor f ≪≫ e.symm ≪≫ (leftUnitor s).symm

theorem qUnitCell_even {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (qUnitCell p q f s e).hom ∈ parity (R := k) _ _ 0 := by
  subst a' b'
  change s ≅ f at e
  change e.hom ∈ parity (R := k) (C := O a ⟶ O b) s f 0 at he
  change (rightUnitor f).hom ≫ e.inv ≫ (leftUnitor s).inv ∈
    parity (R := k) (C := O a ⟶ O b) _ _ 0
  simpa only [add_zero] using comp_mem (C := O a ⟶ O b) (rightUnitor_hom_mem f)
    (comp_mem (C := O a ⟶ O b) (inv_mem (C := O a ⟶ O b) e he)
      (inv_mem (C := O a ⟶ O b) (leftUnitor s) (leftUnitor_hom_mem (R := k) s)))

theorem qUnitCell_degree {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b') (e : s ≅ (qUnitTransport p q).obj f)
    (he : e.hom ∈ degree (R := k) _ _ 0) :
    (qUnitCell p q f s e).hom ∈ degree (R := k) _ _ 0 := by
  subst a' b'
  change s ≅ f at e
  change e.hom ∈ degree (R := k) (C := O a ⟶ O b) s f 0 at he
  change (rightUnitor f).hom ≫ e.inv ≫ (leftUnitor s).inv ∈
    degree (R := k) (C := O a ⟶ O b) _ _ 0
  have hi : e.inv ∈ degree (R := k) (C := O a ⟶ O b) f s 0 := by
    simpa only [neg_zero] using inv_mem_degree (C := O a ⟶ O b) e he
  simpa only [add_zero] using comp_mem_degree (C := O a ⟶ O b)
    (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := k) f)
    (comp_mem_degree (C := O a ⟶ O b) hi
      (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := k) s))

theorem qUnitCell_naturality {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') {f g : O a ⟶ O b} {s t : O a' ⟶ O b'}
    (e : s ≅ (qUnitTransport p q).obj f)
    (e' : t ≅ (qUnitTransport p q).obj g) (η : f ⟶ g) (θ : s ⟶ t)
    (h : θ ≫ e'.hom = e.hom ≫ (qUnitTransport p q).map η) :
    η ▷ qUnitObj q ≫ (qUnitCell p q g t e').hom =
      (qUnitCell p q f s e).hom ≫ qUnitObj p ◁ θ := by
  subst a' b'
  change s ≅ f at e
  change t ≅ g at e'
  change θ ≫ e'.hom = e.hom ≫ η at h
  have hi : η ≫ e'.inv = e.inv ≫ θ := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  change η ▷ 𝟙 _ ≫ (rightUnitor g).hom ≫ e'.inv ≫ (leftUnitor t).inv =
    ((rightUnitor f).hom ≫ e.inv ≫ (leftUnitor s).inv) ≫ 𝟙 _ ◁ θ
  rw [rightUnitor_naturality_assoc k, reassoc_of% hi, leftUnitor_inv_naturality k]
  simp only [Category.assoc]

theorem qUnitCell_comp {a b c a' b' c' : UGr D Sc sy hc}
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
    (𝟙 (f ≫ g)) ▷ qUnitObj r ≫ (qUnitCell p r (f ≫ g) z e'').hom =
      (associator f g (qUnitObj r)).hom ≫ f ◁ (qUnitCell q r g t e').hom ≫
      (associator f (qUnitObj q) t).inv ≫ (qUnitCell p q f s e).hom ▷ t ≫
      (associator (qUnitObj p) s t).hom ≫ qUnitObj p ◁ κ := by
  subst a' b' c'
  change s ≅ f at e
  change t ≅ g at e'
  change z ≅ f ≫ g at e''
  change e.hom ∈ parity (R := k) (C := O a ⟶ O b) s f 0 at he
  change κ ≫ e''.hom = e.hom ▷ t ≫ f ◁ e'.hom ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  have hi : e''.inv = e.inv ▷ g ≫ s ◁ e'.inv ≫ κ := by
    apply (cancel_mono e''.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [h, ← whisker_exchange_of_even_left_assoc he,
      inv_hom_whiskerRight_assoc k, whiskerLeft_inv_hom k]
  change (𝟙 (f ≫ g)) ▷ 𝟙 _ ≫ (rightUnitor (f ≫ g)).hom ≫ e''.inv ≫ (leftUnitor z).inv =
    (associator f g (𝟙 _)).hom ≫ f ◁ ((rightUnitor g).hom ≫ e'.inv ≫ (leftUnitor t).inv) ≫
      (associator f (𝟙 _) t).inv ≫ ((rightUnitor f).hom ≫ e.inv ≫ (leftUnitor s).inv) ▷ t ≫
      (associator (𝟙 _) s t).hom ≫ 𝟙 _ ◁ κ
  have tri : (associator f (𝟙 _) t).inv ≫ (rightUnitor f).hom ▷ t =
      f ◁ (leftUnitor t).hom := by
    rw [← TwoSupercategory.triangle (R := k), Iso.inv_hom_id_assoc]
  simp only [whiskerLeft_comp' k, comp_whiskerRight' k, id_whiskerRight (R := k),
    Category.id_comp, Category.assoc]
  rw [reassoc_of% tri, whiskerLeft_inv_hom_assoc k,
    ← leftUnitor_comp_inv_assoc k s t, ← leftUnitor_inv_naturality k,
    ← Category.assoc (associator f g (𝟙 _)).hom, ← rightUnitor_comp k f g]
  rw [hi]
  simp only [Category.assoc]
  rw [whisker_exchange_of_even_left_assoc (inv_mem (C := O a ⟶ O b) e he)]

theorem qUnitCell_id {a a' : UGr D Sc sy hc} (p : a = a')
    (s : O a' ⟶ O a') (e : s ≅ (qUnitTransport p p).obj (𝟙 (O a)))
    (κ : 𝟙 (O a') ⟶ s)
    (h : κ ≫ e.hom = eqToHom (qUnitTransport_id p).symm) :
    (rightUnitor (qUnitObj p)).hom ≫ (leftUnitor (qUnitObj p)).inv ≫
      (𝟙 (𝟙 (O a))) ▷ qUnitObj p ≫ (qUnitCell p p (𝟙 (O a)) s e).hom =
      qUnitObj p ◁ κ := by
  subst a'
  change s ≅ 𝟙 (O a) at e
  change κ ≫ e.hom = 𝟙 (𝟙 (O a)) at h
  have hi : e.inv = κ := by
    apply (cancel_mono e.hom).mp
    rw [Iso.inv_hom_id, h]
  change (rightUnitor (𝟙 (O a))).hom ≫ (leftUnitor (𝟙 (O a))).inv ≫
    (𝟙 (𝟙 (O a))) ▷ 𝟙 (O a) ≫ (rightUnitor (𝟙 (O a))).hom ≫ e.inv ≫
      (leftUnitor s).inv = 𝟙 (O a) ◁ κ
  rw [hi, leftUnitor_inv_naturality k]
  simp only [unitors_inv_equal k, id_whiskerRight (R := k), Category.id_comp,
    Iso.hom_inv_id_assoc]
end OddMath.SKM

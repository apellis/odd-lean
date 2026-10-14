/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitLocal

/-!
# Reflection of composition and identity equations

Equations for composites and identities, reflected through the faithful hom functors of `ω_q`.

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

theorem qUnitReflect_comp_base {a b c : A} (f : a ⟶ b) (g : b ⟶ c)
    (s : a ⟶ b) (t : b ⟶ c) (z : a ⟶ c)
    (e : s ≅ f) (e' : t ≅ g) (e'' : z ≅ f ≫ g) (κ : s ≫ t ⟶ z)
    (ε : (F).map s ⟶ (F).map f) (ε' : (F).map t ⟶ (F).map g)
    (ε'' : (F).map z ⟶ (F).map (f ≫ g))
    (he : (F).map₂ e.hom = ε ≫ 𝟙 _)
    (he' : (F).map₂ e'.hom = ε' ≫ 𝟙 _)
    (he'' : (F).map₂ e''.hom = ε'' ≫ 𝟙 _)
    (h : ((F).mapComp s t).hom ≫ (F).map₂ κ ≫ ε'' =
      ε ▷ (F).map t ≫ (F).map f ◁ ε' ≫ 𝟙 _ ≫ ((F).mapComp f g).hom) :
    κ ≫ e''.hom = e.hom ▷ t ≫ f ◁ e'.hom ≫ 𝟙 _ := by
  simp only [Category.comp_id] at he he' he'' ⊢
  rw [Category.id_comp, ← he, ← he', ← he''] at h
  apply (chevQHom a.as c.as).map_injective
  change (F).map₂ _ = (F).map₂ _
  rw [(F).map₂_comp, (F).map₂_comp]
  apply (cancel_epi ((F).mapComp s t).hom).mp
  rw [← (F).mapComp_naturality_left_assoc, ← (F).mapComp_naturality_right]
  exact h

theorem qUnitReflect_id_base (a : A) (s : a ⟶ a) (e : s ≅ 𝟙 a)
    (κ : 𝟙 a ⟶ s) (ε : (F).map s ⟶ (F).map (𝟙 a))
    (he : (F).map₂ e.hom = ε ≫ 𝟙 _)
    (h : ((F).mapId a).hom ≫ (F).map₂ κ ≫ ε = 𝟙 _ ≫ ((F).mapId a).hom) :
    κ ≫ e.hom = 𝟙 _ := by
  rw [Category.comp_id] at he
  rw [Category.id_comp, ← he] at h
  apply (chevQHom a.as a.as).map_injective
  change (F).map₂ _ = (F).map₂ _
  rw [(F).map₂_comp, (F).map₂_id]
  apply (cancel_epi ((F).mapId a).hom).mp
  rw [Category.comp_id]
  exact h
end OddMath.SKM

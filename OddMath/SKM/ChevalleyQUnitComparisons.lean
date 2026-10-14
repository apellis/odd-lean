/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitReflection

/-!
# The hom counit and the comparisons

Compatibility of `qUnitHomCounit` with composition and identities.

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

private theorem unitPaste {C : Type*} [Category C] {a b c d e f : C}
    (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) (δ : d ⟶ e)
    (ε : c ⟶ f) (ζ : f ⟶ e) (τ : a ⟶ f) (ω : b ⟶ d)
    (hm : ω = β ≫ γ) (h : γ ≫ δ = ε ≫ ζ) (h' : (α ≫ β) ≫ ε = τ) :
    α ≫ ω ≫ δ = τ ≫ ζ := by
  rw [hm, Category.assoc, h, ← Category.assoc β, ← Category.assoc α,
    ← Category.assoc α β, h']

private theorem unitPasteComp {C : Type*} [Category C] {a b c d e f x y : C}
    (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) (δ : d ⟶ e)
    (ε : c ⟶ f) (ζ : f ⟶ e) (ρ : a ⟶ x) (σ : x ⟶ y) (τ : y ⟶ f) (ω : b ⟶ d)
    (hm : ω = β ≫ γ) (h : γ ≫ δ = ε ≫ ζ) (h' : (α ≫ β) ≫ ε = ρ ≫ σ ≫ τ) :
    α ≫ ω ≫ δ = ρ ≫ σ ≫ τ ≫ ζ := by
  rw [unitPaste α β γ δ ε ζ (ρ ≫ σ ≫ τ) ω hm h h']
  simp only [Category.assoc]

theorem qUnitHomCounit_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    ((H).mapComp f g).hom ≫ (qUnitHomCounit (f ≫ g)).hom =
      (qUnitHomCounit f).hom ▷ (H).map g ≫
      (show (H).obj a ⟶ (H).obj b from (qUnitHomTransport a b).obj f) ◁
        (qUnitHomCounit g).hom ≫
      eqToHom (qUnitTransport_comp (chevQ_negWeight_square a.as).symm
        (chevQ_negWeight_square b.as).symm (chevQ_negWeight_square c.as).symm f g).symm := by
  apply qUnitReflect_comp (chevQ_negWeight_square a.as).symm
    (chevQ_negWeight_square b.as).symm (chevQ_negWeight_square c.as).symm
    f g ((H).map f) ((H).map g) ((H).map (f ≫ g))
    (qUnitHomCounit f) (qUnitHomCounit g) (qUnitHomCounit (f ≫ g)) ((H).mapComp f g).hom
    (chevalleyQReverseHomCounit ((F).map f)).hom
    (chevalleyQReverseHomCounit ((F).map g)).hom
    (chevalleyQReverseHomCounit ((F).map (f ≫ g))).hom
    (qUnitHomCounit_image f) (qUnitHomCounit_image g) (qUnitHomCounit_image (f ≫ g))
  let aa : A := (H).obj a
  let cc : A := (H).obj c
  let aa' : B := (F).obj aa
  let cc' : B := (F).obj cc
  let L : (aa ⟶ cc) ⥤ (aa' ⟶ cc') := (F).mapFunctor aa cc
  have hm : (F).map₂ ((H).mapComp f g).hom =
      L.map ((G).mapComp ((F).map f) ((F).map g)).hom ≫
        L.map ((G).map₂ ((F).mapComp f g).hom) :=
    L.map_comp _ _
  exact unitPasteComp _ _ _ _ _ _ _ _ _ _ hm
    (chevalleyQReverseHomCounit_naturality ((F).mapComp f g).hom)
    (qGlobalCounit_comp_image ((F).map f) ((F).map g))

theorem qUnitHomCounit_id (a : A) :
    ((H).mapId a).hom ≫ (qUnitHomCounit (𝟙 a)).hom =
      eqToHom (qUnitTransport_id (chevQ_negWeight_square a.as).symm).symm := by
  apply qUnitReflect_id (chevQ_negWeight_square a.as).symm
    ((H).map (𝟙 a)) (qUnitHomCounit (𝟙 a)) ((H).mapId a).hom
    (chevalleyQReverseHomCounit ((F).map (𝟙 a))).hom (qUnitHomCounit_image (𝟙 a))
  let aa : A := (H).obj a
  let aa' : B := (F).obj aa
  let L : (aa ⟶ aa) ⥤ (aa' ⟶ aa') := (F).mapFunctor aa aa
  have hm : (F).map₂ ((H).mapId a).hom =
      L.map ((G).mapId ((F).obj a)).hom ≫ L.map ((G).map₂ ((F).mapId a).hom) :=
    L.map_comp _ _
  exact unitPaste _ _ _ _ _ _ _ _ hm
    (chevalleyQReverseHomCounit_naturality ((F).mapId a).hom)
    (qGlobalCounit_id_image ((F).obj a))
end OddMath.SKM

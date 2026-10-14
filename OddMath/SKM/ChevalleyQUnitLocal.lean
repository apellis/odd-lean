/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitEndpoint

/-!
# The hom counit is even and natural

`qUnitHomCounit` is even of degree zero and natural in 2-morphisms.

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

private theorem unitEq_degree {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] [GradedSupercategory k C]
    {x y : C} (p : x = y) : eqToHom p ∈ degree (R := k) x y 0 := by
  subst y
  exact id_mem_degree _

theorem qUnitHomCounit_even {a b : A} (f : a ⟶ b) :
    (qUnitHomCounit f).hom ∈ parity (R := k) _ _ 0 := by
  apply q_bundled_reflect_parity ((H).obj a) ((H).obj b)
  rw [qUnitHomCounit_image]
  let aa : B := (F).obj ((H).obj a)
  let bb : B := (F).obj ((H).obj b)
  let x : aa ⟶ bb := (F).map ((H).map f)
  let y : aa ⟶ bb := (chevalleyQReverseTransport ((F).obj a) ((F).obj b)).obj ((F).map f)
  let z : aa ⟶ bb := (F).map ((qUnitHomTransport a b).obj f)
  let e : x ≅ y := chevalleyQReverseHomCounit ((F).map f)
  let p : z = y := qUnitTransport_forward (chevQ_negWeight_square a.as).symm
    (chevQ_negWeight_square b.as).symm f
  change e.hom ≫ eqToHom p.symm ∈ parity (R := k) (C := aa ⟶ bb) x z 0
  have he : e.hom ∈ parity (R := k) (C := aa ⟶ bb) x y 0 :=
    chevalleyQReverseHomCounit_even ((F).map f)
  simpa only [add_zero] using comp_mem (C := aa ⟶ bb) he (eqToHom_mem (R := k) p.symm)

theorem qUnitHomCounit_degree {a b : A} (f : a ⟶ b) :
    (qUnitHomCounit f).hom ∈ degree (R := k) _ _ 0 := by
  apply q_bundled_reflect_degree ((H).obj a) ((H).obj b)
  rw [qUnitHomCounit_image]
  let aa : B := (F).obj ((H).obj a)
  let bb : B := (F).obj ((H).obj b)
  let x : aa ⟶ bb := (F).map ((H).map f)
  let y : aa ⟶ bb := (chevalleyQReverseTransport ((F).obj a) ((F).obj b)).obj ((F).map f)
  let z : aa ⟶ bb := (F).map ((qUnitHomTransport a b).obj f)
  let e : x ≅ y := chevalleyQReverseHomCounit ((F).map f)
  let p : z = y := qUnitTransport_forward (chevQ_negWeight_square a.as).symm
    (chevQ_negWeight_square b.as).symm f
  change e.hom ≫ eqToHom p.symm ∈ degree (R := k) (C := aa ⟶ bb) x z 0
  have he : e.hom ∈ degree (R := k) (C := aa ⟶ bb) x y 0 :=
    chevalleyQReverseHomCounit_degree ((F).map f)
  simpa only [add_zero] using comp_mem_degree (C := aa ⟶ bb) he (unitEq_degree p.symm)

private theorem unitNaturality {C C' : Type*} [Category C] [Category C']
    (L : C ⥤ C') [L.Faithful] {s t x y : C} {u v : C'}
    (e : s ≅ x) (e' : t ≅ y) (i : L.obj x ≅ u) (j : L.obj y ≅ v)
    (ε : L.obj s ⟶ u) (ε' : L.obj t ⟶ v)
    (θ : s ⟶ t) (η : x ⟶ y) (μ : u ⟶ v)
    (he : L.map e.hom = ε ≫ i.inv) (he' : L.map e'.hom = ε' ≫ j.inv)
    (hn : L.map θ ≫ ε' = ε ≫ μ)
    (ht : L.map η ≫ j.hom = i.hom ≫ μ) : θ ≫ e'.hom = e.hom ≫ η := by
  apply L.map_injective
  rw [L.map_comp, L.map_comp, he, he']
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ht, Iso.inv_hom_id_assoc, hn]

theorem qUnitHomCounit_naturality {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    (H).map₂ η ≫ (qUnitHomCounit g).hom = (qUnitHomCounit f).hom ≫
      (qUnitHomTransport a b).map η := by
  let aa : A := (H).obj a
  let bb : A := (H).obj b
  let aa' : B := (F).obj aa
  let bb' : B := (F).obj bb
  let L : (aa ⟶ bb) ⥤ (aa' ⟶ bb') := (F).mapFunctor aa bb
  let : L.Faithful := inferInstanceAs (chevQHom aa.as bb.as).Faithful
  exact unitNaturality L (qUnitHomCounit f) (qUnitHomCounit g)
    (eqToIso (qUnitTransport_forward (chevQ_negWeight_square a.as).symm
      (chevQ_negWeight_square b.as).symm f))
    (eqToIso (qUnitTransport_forward (chevQ_negWeight_square a.as).symm
      (chevQ_negWeight_square b.as).symm g))
    (chevalleyQReverseHomCounit ((F).map f)).hom
    (chevalleyQReverseHomCounit ((F).map g)).hom
    ((H).map₂ η) ((qUnitHomTransport a b).map η)
    ((chevalleyQReverseTransport ((F).obj a) ((F).obj b)).map ((F).map₂ η))
    (qUnitHomCounit_image f) (qUnitHomCounit_image g)
    (chevalleyQReverseHomCounit_naturality ((F).map₂ η))
    (qUnitTransport_forward_map _ _ η)
end OddMath.SKM

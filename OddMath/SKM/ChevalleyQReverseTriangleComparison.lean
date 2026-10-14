/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTriangleComponent

/-!
# Comparison for the second triangle of `ω_q`

Compatibility of the inverse hom functors with endpoint transport, used in the second triangle.

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
local notation "B" => TwoSOp k A
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "O" a:max => (⟨⟨a⟩⟩ : B)
local notation "N" => negWeight (D := D) (Sc := Sc) (sy := sy) (hc := hc)

theorem qReverseTransport_counit_obj {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (f : O a ⟶ O b) :
    (chevalleyQReverseTransport (O a') (O b')).obj ((chevQEndpointTransport p q).obj f) =
      (chevQEndpointTransport (congrArg (fun a => N (N a)) p)
        (congrArg (fun b => N (N b)) q)).obj ((chevalleyQReverseTransport (O a) (O b)).obj f) := by
  subst a' b'
  rfl

theorem qReverseTransport_counit {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (f : O a ⟶ O b) :
    (F).map₂ (eqToHom (qReverseTransport_obj p q f)) ≫
      eqToHom (qUnitTransport_forward (congrArg N p) (congrArg N q) ((G).map f)) ≫
      (chevQEndpointTransport (congrArg (fun a => N (N a)) p)
        (congrArg (fun b => N (N b)) q)).map (chevalleyQReverseHomCounit f).hom =
    (chevalleyQReverseHomCounit (c := O a') (d := O b')
      ((chevQEndpointTransport p q).obj f)).hom ≫
        eqToHom (qReverseTransport_counit_obj p q f) := by
  subst a' b'
  change (F).map₂ (𝟙 ((G).map f)) ≫ 𝟙 _ ≫ (chevalleyQReverseHomCounit f).hom =
    (chevalleyQReverseHomCounit f).hom ≫ 𝟙 _
  rw [(F).map₂_id]
  exact (Category.id_comp (obj := (F).obj ((G).obj (O a)) ⟶
    (F).obj ((G).obj (O b))) _).trans
    ((Category.id_comp (obj := (F).obj ((G).obj (O a)) ⟶
      (F).obj ((G).obj (O b))) _).trans
      (Category.comp_id (obj := (F).obj ((G).obj (O a)) ⟶
        (F).obj ((G).obj (O b))) _).symm)

private theorem reverseCounitReflection {C C' : Type*} [Category C] [Category C']
    (L : C ⥤ C') [L.Faithful] {s t z : C} {x y : C'}
    (η : s ⟶ t) (θ : t ⟶ z) (d : s ⟶ z)
    (e : L.obj s ≅ x) (e' : L.obj t ≅ y) (i : L.obj z ≅ x) (μ : x ≅ y)
    (hn : L.map η ≫ e'.hom = e.hom ≫ μ.hom)
    (ht : L.map θ ≫ i.hom ≫ μ.hom = e'.hom)
    (hd : L.map d = e.hom ≫ i.inv) : η ≫ θ = d := by
  apply L.map_injective
  rw [L.map_comp, hd]
  apply (cancel_mono i.hom).mp
  apply (cancel_mono μ.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [ht, hn]

theorem qReverseHomCounit_comparison {a b : B} (f : a ⟶ b) :
    (G).map₂ (chevalleyQReverseHomCounit f).hom ≫
      eqToHom (qReverseTransport_obj (chevQ_negWeight_square a.unop.as).symm
        (chevQ_negWeight_square b.unop.as).symm f) =
      (qUnitHomCounit ((G).map f)).hom := by
  let p := (chevQ_negWeight_square a.unop.as).symm
  let q := (chevQ_negWeight_square b.unop.as).symm
  let aa : A := (G).obj ((F).obj ((G).obj a))
  let bb : A := (G).obj ((F).obj ((G).obj b))
  let L : (aa ⟶ bb) ⥤ ((F).obj aa ⟶ (F).obj bb) := (F).mapFunctor aa bb
  let : L.Faithful := inferInstanceAs (chevQHom aa.as bb.as).Faithful
  let s : aa ⟶ bb := (G).map ((F).map ((G).map f))
  let t : aa ⟶ bb := (G).map (a := (F).obj ((G).obj a))
    (b := (F).obj ((G).obj b)) ((chevalleyQReverseTransport a b).obj f)
  let z : aa ⟶ bb := (qUnitHomTransport ((G).obj a) ((G).obj b)).obj ((G).map f)
  let e : L.obj s ≅ (chevalleyQReverseTransport ((F).obj ((G).obj a))
    ((F).obj ((G).obj b))).obj ((F).map ((G).map f)) :=
    chevalleyQReverseHomCounit ((F).map ((G).map f))
  let μ := (chevalleyQReverseTransport ((F).obj ((G).obj a))
    ((F).obj ((G).obj b))).mapIso (chevalleyQReverseHomCounit f)
  let e' : L.obj t ≅ (chevalleyQReverseTransport ((F).obj ((G).obj a))
    ((F).obj ((G).obj b))).obj ((chevalleyQReverseTransport a b).obj f) :=
    chevalleyQReverseHomCounit (c := (F).obj ((G).obj a)) (d := (F).obj ((G).obj b))
      ((chevalleyQReverseTransport a b).obj f)
  let i : L.obj z ≅ (chevalleyQReverseTransport ((F).obj ((G).obj a))
    ((F).obj ((G).obj b))).obj ((F).map ((G).map f)) :=
    eqToIso (qUnitTransport_forward (congrArg N p) (congrArg N q) ((G).map f))
  apply reverseCounitReflection L _ _ _ e e' i μ
  · exact chevalleyQReverseHomCounit_naturality (chevalleyQReverseHomCounit f).hom
  · have h := qReverseTransport_counit p q f
    change L.map (eqToHom (qReverseTransport_obj p q f)) ≫ i.hom ≫ μ.hom =
      e'.hom ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id (obj := (F).obj aa ⟶ (F).obj bb) _)
  · exact qUnitHomCounit_image ((G).map f)

end OddMath.SKM

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQCounitInvTransport

/-!
# The inverse counit of `ω_q`

`chevalleyQGlobalCounitInv : 1 ⟹ G_q ⋙ ω_q`, a strong graded 2-natural transformation.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "B" => TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (G) (F)

def chevalleyQGlobalCounitInvObj (a : B) : a ⟶ (H).obj a :=
  qCounitInvObj (chevQ_negWeight_square a.unop.as).symm

def chevalleyQGlobalCounitInvCell {a b : B} (f : a ⟶ b) :
    f ≫ chevalleyQGlobalCounitInvObj b ≅ chevalleyQGlobalCounitInvObj a ≫ (H).map f :=
  qCounitInvCell (chevQ_negWeight_square a.unop.as).symm
    (chevQ_negWeight_square b.unop.as).symm f ((H).map f) (chevalleyQReverseHomCounit f)

/-- Reverse to the counit on the same category, not the global unit on the other category. -/
def chevalleyQGlobalCounitInv : TwoNatTrans (TwoSuperfunctor.id k B) (H) where
  X := chevalleyQGlobalCounitInvObj
  x f := (chevalleyQGlobalCounitInvCell f).hom
  x_mem f := qCounitInvCell_even _ _ _ _ _ (chevalleyQReverseHomCounit_even f)
  naturality η := qCounitInvCell_naturality _ _ _ _ η ((H).map₂ η)
    (chevalleyQReverseHomCounit_naturality η)
  x_comp f g := qCounitInvCell_comp _ _ _ f g ((H).map f) ((H).map g) ((H).map (f ≫ g))
    (chevalleyQReverseHomCounit f) (chevalleyQReverseHomCounit g)
    (chevalleyQReverseHomCounit (f ≫ g)) ((H).mapComp f g).hom
    (chevalleyQReverseHomCounit_even f) (qGlobalCounit_comp_image f g)
  x_id a := qCounitInvCell_id _ ((H).map (𝟙 a)) (chevalleyQReverseHomCounit (𝟙 a))
    ((H).mapId a).hom (qGlobalCounit_id_image a)

theorem chevalleyQGlobalCounitInv_isStrong :
    (chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsStrong :=
  fun f => inferInstanceAs (IsIso (chevalleyQGlobalCounitInvCell f).hom)

theorem chevalleyQGlobalCounitInv_isGraded :
    (chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsGraded :=
  fun f => qCounitInvCell_degree _ _ _ _ _ (chevalleyQReverseHomCounit_degree f)
end OddMath.SKM

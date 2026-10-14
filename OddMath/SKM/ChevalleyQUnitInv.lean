/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitInvTransport

/-!
# The inverse unit of `ω_q`

`chevalleyQGlobalUnitInv : ω_q ⋙ G_q ⟹ 1`, a strong graded 2-natural transformation.

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
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (F) (G)

def chevalleyQGlobalUnitInvObj (a : A) : (H).obj a ⟶ a :=
  qUnitInvObj (chevQ_negWeight_square a.as).symm

def chevalleyQGlobalUnitInvCell {a b : A} (f : a ⟶ b) :
    (H).map f ≫ chevalleyQGlobalUnitInvObj b ≅ chevalleyQGlobalUnitInvObj a ≫ f :=
  qUnitInvCell (chevQ_negWeight_square a.as).symm
    (chevQ_negWeight_square b.as).symm f ((H).map f) (qUnitHomCounit f)

/-- Reverse after forward to the identity, on the envelope. -/
def chevalleyQGlobalUnitInv : TwoNatTrans (H) (TwoSuperfunctor.id k A) where
  X := chevalleyQGlobalUnitInvObj
  x f := (chevalleyQGlobalUnitInvCell f).hom
  x_mem f := qUnitInvCell_even _ _ _ _ _ (qUnitHomCounit_even f)
  naturality η := qUnitInvCell_naturality _ _ _ _ η ((H).map₂ η)
    (qUnitHomCounit_naturality η)
  x_comp f g := qUnitInvCell_comp _ _ _ f g ((H).map f) ((H).map g) ((H).map (f ≫ g))
    (qUnitHomCounit f) (qUnitHomCounit g)
    (qUnitHomCounit (f ≫ g)) ((H).mapComp f g).hom
    (qUnitHomCounit_even f) (qUnitHomCounit_comp f g)
  x_id a := qUnitInvCell_id _ ((H).map (𝟙 a)) (qUnitHomCounit (𝟙 a))
    ((H).mapId a).hom (qUnitHomCounit_id a)

theorem chevalleyQGlobalUnitInv_isStrong :
    (chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsStrong :=
  fun f => inferInstanceAs (IsIso (chevalleyQGlobalUnitInvCell f).hom)

theorem chevalleyQGlobalUnitInv_isGraded :
    (chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsGraded :=
  fun f => qUnitInvCell_degree _ _ _ _ _ (qUnitHomCounit_degree f)
end OddMath.SKM

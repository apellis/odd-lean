/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitTransport

/-!
# The unit of `ω_q`

`chevalleyQGlobalUnit : 1 ⟹ ω_q ⋙ G_q`, a strong graded 2-natural transformation on `𝔘_q(𝔤)`.

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

def chevalleyQGlobalUnitObj (a : A) : a ⟶ (H).obj a :=
  qUnitObj (chevQ_negWeight_square a.as).symm

def chevalleyQGlobalUnitCell {a b : A} (f : a ⟶ b) :
    f ≫ chevalleyQGlobalUnitObj b ≅ chevalleyQGlobalUnitObj a ≫ (H).map f :=
  qUnitCell (chevQ_negWeight_square a.as).symm
    (chevQ_negWeight_square b.as).symm f ((H).map f) (qUnitHomCounit f)

/-- The unit on the source of the Chevalley Q two-superfunctor.
The composite is diagrammatic: reverse after forward. The comparison fields use
its signed comparisons, without a strictness or global-coherence hypothesis. -/
def chevalleyQGlobalUnit : TwoNatTrans (TwoSuperfunctor.id k A) (H) where
  X := chevalleyQGlobalUnitObj
  x f := (chevalleyQGlobalUnitCell f).hom
  x_mem f := qUnitCell_even _ _ _ _ _ (qUnitHomCounit_even f)
  naturality η := qUnitCell_naturality _ _ _ _ η ((H).map₂ η)
    (qUnitHomCounit_naturality η)
  x_comp f g := qUnitCell_comp _ _ _ f g ((H).map f) ((H).map g) ((H).map (f ≫ g))
    (qUnitHomCounit f) (qUnitHomCounit g)
    (qUnitHomCounit (f ≫ g)) ((H).mapComp f g).hom
    (qUnitHomCounit_even f) (qUnitHomCounit_comp f g)
  x_id a := qUnitCell_id _ ((H).map (𝟙 a)) (qUnitHomCounit (𝟙 a))
    ((H).mapId a).hom (qUnitHomCounit_id a)

theorem chevalleyQGlobalUnit_isStrong :
    (chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsStrong :=
  fun f => inferInstanceAs (IsIso (chevalleyQGlobalUnitCell f).hom)

theorem chevalleyQGlobalUnit_isGraded :
    (chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsGraded :=
  fun f => qUnitCell_degree _ _ _ _ _ (qUnitHomCounit_degree f)
end OddMath.SKM

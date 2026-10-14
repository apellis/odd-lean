/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiUnitInv

/-!
# Cancellation isomorphisms for the unit of `ω̃`

The two isomorphisms from the composites of the unit of `ω̃` and its inverse to identity transformations.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "Aπ" => QPiTwoEnvelope k (UGr D Sc sy hc)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "J" => chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "K" => chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Jπ" => chevalleyQPiGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Kπ" => chevalleyQPiGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Cancellation of the unit followed by its lifted reverse. -/
def qPiUnitCancel : EvenIso ((Jπ).vcomp (Kπ)) (TwoNatTrans.id (TwoSuperfunctor.id k (Aπ))) :=
  EvenIso.rebaseCancel (TwoEnvelope.mapPi_id k (A)) (qPiUnit_target (D := D) (Sc := Sc))
    (TwoEnvelope.mapPiNatTrans (J)) (TwoEnvelope.mapPiNatTrans (K))
    (EvenIso.mapPiCancel (J) (K) ⟨chevalleyQGlobalUnitCompIso,
      chevalleyQGlobalUnitCompIso_homogeneous, chevalleyQGlobalUnitCompIso_inv_homogeneous⟩)

/-- Cancellation in the other order, at the composite. -/
def qPiUnitInvCancel : EvenIso ((Kπ).vcomp (Jπ)) (TwoNatTrans.id ((Fπ).comp (Gπ))) :=
  EvenIso.rebaseCancel (qPiUnit_target (D := D) (Sc := Sc)) (TwoEnvelope.mapPi_id k (A))
    (TwoEnvelope.mapPiNatTrans (K)) (TwoEnvelope.mapPiNatTrans (J))
    (EvenIso.mapPiCancel (K) (J) ⟨chevalleyQGlobalUnitInvCompIso,
      chevalleyQGlobalUnitInvCompIso_homogeneous, chevalleyQGlobalUnitInvCompIso_inv_homogeneous⟩)

/-- An isomorphism in the modification category, not merely objectwise cancellation. -/
def chevalleyQPiGlobalUnitCompIso :
    (Jπ).vcomp (Kπ) ≅ TwoNatTrans.id (TwoSuperfunctor.id k (Aπ)) :=
  (qPiUnitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1

/-- The reverse-order modification-category isomorphism. -/
def chevalleyQPiGlobalUnitInvCompIso :
    (Kπ).vcomp (Jπ) ≅ TwoNatTrans.id ((Fπ).comp (Gπ)) :=
  (qPiUnitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1
end OddMath.SKM

namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem chevalleyQPiGlobalUnitCompIso_eq :
    chevalleyQPiGlobalUnitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiUnitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

theorem chevalleyQPiGlobalUnitInvCompIso_eq :
    chevalleyQPiGlobalUnitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiUnitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

end OddMath.SKM

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiUnitCancelIso

/-!
# The unit of `ω̃` is invertible

Both cancellation isomorphisms of the unit of `ω̃` are even of degree zero.

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

theorem chevalleyQPiGlobalUnitCompIso_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalUnitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Jπ).vcomp (Kπ) ≅ TwoNatTrans.id (TwoSuperfunctor.id k (Aπ)) =>
      Supermodification.IsHomogeneous (R := k) z.hom 0 0)
    (chevalleyQPiGlobalUnitCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiUnitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiGlobalUnitCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalUnitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Jπ).vcomp (Kπ) ≅ TwoNatTrans.id (TwoSuperfunctor.id k (Aπ)) =>
      Supermodification.IsHomogeneous (R := k) z.inv 0 0)
    (chevalleyQPiGlobalUnitCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiUnitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2

theorem chevalleyQPiGlobalUnitInvCompIso_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalUnitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Kπ).vcomp (Jπ) ≅ TwoNatTrans.id ((Fπ).comp (Gπ)) =>
      Supermodification.IsHomogeneous (R := k) z.hom 0 0)
    (chevalleyQPiGlobalUnitInvCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiUnitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiGlobalUnitInvCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalUnitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Kπ).vcomp (Jπ) ≅ TwoNatTrans.id ((Fπ).comp (Gπ)) =>
      Supermodification.IsHomogeneous (R := k) z.inv 0 0)
    (chevalleyQPiGlobalUnitInvCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiUnitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2

end OddMath.SKM

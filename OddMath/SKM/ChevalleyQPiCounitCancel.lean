/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiCounitInv
import OddMath.SKM.ChevalleyQPiUnitInv

/-!
# The counit of `ω̃` is invertible

Even invertible modifications of degree zero from both composites of the counit of `ω̃` and its inverse to identity transformations.

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
local notation "T" => TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc))
local notation "P" => PiSOp.twoFunctor (R := k) (B := A)
local notation "P⁻" => PiSOp.inverseTwoFunctor (R := k) (B := A)
local notation "E" => chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "L" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Eπ" => chevalleyQPiGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Lπ" => chevalleyQPiGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (Gπ) (Fπ)
local notation "Id" => TwoSuperfunctor.id k (T)

/-- Lift the two cancellation isomorphisms before conjugation. -/
def qPiCounitLiftCancel := EvenIso.mapPiCancel (E) (L) ⟨chevalleyQGlobalCounitCompIso,
  chevalleyQGlobalCounitCompIso_homogeneous, chevalleyQGlobalCounitCompIso_inv_homogeneous⟩
def qPiCounitLiftInvCancel := EvenIso.mapPiCancel (L) (E) ⟨chevalleyQGlobalCounitInvCompIso,
  chevalleyQGlobalCounitInvCompIso_homogeneous, chevalleyQGlobalCounitInvCompIso_inv_homogeneous⟩

/-- Precomposition keeps the complete transformations. -/
def qPiCounitPreCancel := EvenIso.precomposeCancel (P⁻) _ _
  (qPiCounitLiftCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc))
def qPiCounitPreInvCancel := EvenIso.precomposeCancel (P⁻) _ _
  (qPiCounitLiftInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc))

/-- Postcomposition retains both its compositor and its identity comparison. -/
def qPiCounitPostCancel := EvenIso.postcomposeCancel (P) PiSOp.twoFunctor_isGraded _ _
  (qPiCounitPreCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc))
def qPiCounitPostInvCancel := EvenIso.postcomposeCancel (P) PiSOp.twoFunctor_isGraded _ _
  (qPiCounitPreInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc))

/-- Transport cancellation with the counit's own endpoint eliminator. -/
def qPiCounitRebaseCancel {S S' U U' : TwoSuperfunctor k (T) (T)}
    (p : S = S') (q : U = U') (θ : TwoNatTrans S U) (ψ : TwoNatTrans U S)
    (e : EvenIso (θ.vcomp ψ) (TwoNatTrans.id S)) :
    EvenIso ((qPiRebase p q θ).vcomp (qPiRebase q p ψ)) (TwoNatTrans.id S') := by
  cases p
  cases q
  exact e

/-- Lift, precompose, postcompose with comparisons, then transport the endpoints. -/
def qPiCounitCancel : EvenIso ((Eπ).vcomp (Lπ)) (TwoNatTrans.id (H)) :=
  qPiCounitRebaseCancel (qPiCounit_source (D := D) (Sc := Sc))
    (qPiCounit_target (D := D) (Sc := Sc))
    (qPiCounitConjugate (D := D) (Sc := Sc)) (qPiCounitInvConjugate (D := D) (Sc := Sc))
    (qPiCounitPostCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc))

/-- Reverse-order cancellation uses the same transformations and opposite endpoints. -/
def qPiCounitInvCancel : EvenIso ((Lπ).vcomp (Eπ)) (TwoNatTrans.id (Id)) :=
  qPiCounitRebaseCancel (qPiCounit_target (D := D) (Sc := Sc))
    (qPiCounit_source (D := D) (Sc := Sc))
    (qPiCounitInvConjugate (D := D) (Sc := Sc)) (qPiCounitConjugate (D := D) (Sc := Sc))
    (qPiCounitPostInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc))

/-- Isomorphism in the modification category at the composite. -/
def chevalleyQPiGlobalCounitCompIso : (Eπ).vcomp (Lπ) ≅ TwoNatTrans.id (H) :=
  (qPiCounitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1

/-- Reverse-order modification-category isomorphism at the identity action. -/
def chevalleyQPiGlobalCounitInvCompIso : (Lπ).vcomp (Eπ) ≅ TwoNatTrans.id (Id) :=
  (qPiCounitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1

theorem chevalleyQPiGlobalCounitCompIso_eq :
    chevalleyQPiGlobalCounitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiCounitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

theorem chevalleyQPiGlobalCounitInvCompIso_eq :
    chevalleyQPiGlobalCounitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiCounitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

theorem chevalleyQPiGlobalCounitCompIso_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalCounitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Eπ).vcomp (Lπ) ≅ TwoNatTrans.id (H) =>
      Supermodification.IsHomogeneous (R := k) z.hom 0 0)
    (chevalleyQPiGlobalCounitCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiCounitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiGlobalCounitCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalCounitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Eπ).vcomp (Lπ) ≅ TwoNatTrans.id (H) =>
      Supermodification.IsHomogeneous (R := k) z.inv 0 0)
    (chevalleyQPiGlobalCounitCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiCounitCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2

theorem chevalleyQPiGlobalCounitInvCompIso_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalCounitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Lπ).vcomp (Eπ) ≅ TwoNatTrans.id (Id) =>
      Supermodification.IsHomogeneous (R := k) z.hom 0 0)
    (chevalleyQPiGlobalCounitInvCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiCounitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiGlobalCounitInvCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous (R := k)
      (chevalleyQPiGlobalCounitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv 0 0 := by
  apply Eq.mpr (congrArg
    (fun z : (Lπ).vcomp (Eπ) ≅ TwoNatTrans.id (Id) =>
      Supermodification.IsHomogeneous (R := k) z.inv 0 0)
    (chevalleyQPiGlobalCounitInvCompIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiCounitInvCancel (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2
end OddMath.SKM

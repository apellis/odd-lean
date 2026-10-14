/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiCounit
import OddMath.SKM.ChevalleyQUnit

/-!
# The unit of `ω̃`

`chevalleyQPiGlobalUnit : 1 ⟹ ω̃ ⋙ G̃`, the Π-envelope of the unit of `ω_q`, transported along `mapPi 1 = 1` and the equality of `ω̃ ⋙ G̃` with the Π-envelope of `ω_q ⋙ G_q`.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "Aπ" => QPiTwoEnvelope k (UGr D Sc sy hc)
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "J" => chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Equality of records uses the parity reverse, including comparisons. -/
theorem qPiUnit_composite :
    (TwoEnvelope.mapPi (F)).comp (TwoEnvelope.mapPi (G)) = (Fπ).comp (Gπ) := by
  simp only [chevalleyQPiTwo, chevalleyQPiReverseTwo]
  rw [TwoSuperfunctor.comp_assoc, ← TwoSuperfunctor.comp_assoc PiSOp.twoFunctor,
    PiSOp.twoFunctor_comp_inverseTwoFunctor, TwoSuperfunctor.id_comp]

/-- Complete target equality for the lifted Q unit. -/
theorem qPiUnit_target : TwoEnvelope.mapPi ((F).comp (G)) = (Fπ).comp (Gπ) := by
  rw [TwoEnvelope.mapPi_comp, qPiUnit_composite]

/-- The Q unit, lifted and transported only along endpoint equalities.
No component equivalence or desired coherence is assumed. -/
def chevalleyQPiGlobalUnit : TwoNatTrans (TwoSuperfunctor.id k (Aπ)) ((Fπ).comp (Gπ)) :=
  TwoNatTrans.rebase (TwoEnvelope.mapPi_id k (A))
    (qPiUnit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (TwoEnvelope.mapPiNatTrans (J))

local notation "Jπ" => chevalleyQPiGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Strong means that all naturality cells are invertible. -/
theorem chevalleyQPiGlobalUnit_isStrong : (Jπ).IsStrong := by
  apply TwoNatTrans.rebase_isStrong
  exact TwoEnvelope.mapPiNatTrans_isStrong (θ := J) chevalleyQGlobalUnit_isStrong

/-- Every naturality cell retains integer degree zero. -/
theorem chevalleyQPiGlobalUnit_isGraded : (Jπ).IsGraded := by
  apply TwoNatTrans.rebase_isGraded
  exact TwoEnvelope.mapPiNatTrans_isGraded (θ := J) chevalleyQGlobalUnit_isGraded

/-- The invertible naturality cell of the transported unit. -/
def chevalleyQPiGlobalUnitCell {a b : Aπ} (f : a ⟶ b) :
    (TwoSuperfunctor.id k (Aπ)).map f ≫ (Jπ).X b ≅
      (Jπ).X a ≫ ((Fπ).comp (Gπ)).map f :=
  @asIso _ _ _ _ ((Jπ).x f) (chevalleyQPiGlobalUnit_isStrong f)
end OddMath.SKM

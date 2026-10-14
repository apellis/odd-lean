/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiUnit
import OddMath.SKM.ChevalleyQPiCounitCancel

/-!
# The first zigzag of `ω̃`

`chevalleyQPiForwardZigzag : ω̃ ⟹ ω̃`, the left zigzag `LeftZigzag.zigzag` of the unit and counit of `ω̃`, with its components.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "Aπ" => QPiTwoEnvelope k (UGr D Sc sy hc)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Jπ" => chevalleyQPiGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Eπ" => chevalleyQPiGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- The unit postcomposed by the forward functor. -/
def chevalleyQPiForwardUnitLeg : TwoNatTrans (Fπ) ((Fπ).comp ((Gπ).comp (Fπ))) :=
  TwoNatTrans.rebase (TwoSuperfunctor.id_comp (Fπ))
    (TwoSuperfunctor.comp_assoc (Fπ) (Gπ) (Fπ)) (TwoNatTrans.postcompose (Fπ) (Jπ))

/-- The counit precomposed by the forward functor. -/
def chevalleyQPiForwardCounitLeg : TwoNatTrans ((Fπ).comp ((Gπ).comp (Fπ))) (Fπ) :=
  TwoNatTrans.rebase rfl (TwoSuperfunctor.comp_id (Fπ))
    (TwoNatTrans.precompose (Fπ) (Eπ))

/-- The forward zigzag is the composite of the unit and counit legs. -/
def chevalleyQPiForwardZigzag : TwoNatTrans (Fπ) (Fπ) :=
  chevalleyQPiForwardUnitLeg.vcomp chevalleyQPiForwardCounitLeg

theorem chevalleyQPiForwardUnitLeg_eq :
    chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      LeftZigzag.unitLeg (Fπ) (Gπ) (Jπ) := rfl

theorem chevalleyQPiForwardCounitLeg_eq :
    chevalleyQPiForwardCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      LeftZigzag.counitLeg (Fπ) (Gπ) (Eπ) := rfl

theorem chevalleyQPiForwardZigzag_eq :
    chevalleyQPiForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      LeftZigzag.zigzag (Fπ) (Gπ) (Jπ) (Eπ) := rfl

theorem chevalleyQPiForwardUnitLeg_X (a : Aπ) :
    (chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (Fπ).map ((Jπ).X a) := by
  rw [chevalleyQPiForwardUnitLeg_eq]
  exact LeftZigzag.unitLeg_X (Fπ) (Gπ) (Jπ) a

theorem chevalleyQPiForwardCounitLeg_X (a : Aπ) :
    (chevalleyQPiForwardCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (Eπ).X ((Fπ).obj a) := by
  rw [chevalleyQPiForwardCounitLeg_eq]
  exact LeftZigzag.counitLeg_X (Fπ) (Gπ) (Eπ) a

theorem chevalleyQPiForwardZigzag_X (a : Aπ) :
    (chevalleyQPiForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (Fπ).map ((Jπ).X a) ≫ (Eπ).X ((Fπ).obj a) := by
  rw [chevalleyQPiForwardZigzag_eq]
  exact LeftZigzag.zigzag_X (Fπ) (Gπ) (Jπ) (Eπ) a

theorem chevalleyQPiForwardUnitLeg_x_heq {a b : Aπ} (f : a ⟶ b) :
    HEq ((chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      (TwoNatTrans.postcomposeCell (Fπ) (Jπ) f) := by
  rw [chevalleyQPiForwardUnitLeg_eq]
  exact LeftZigzag.unitLeg_x (Fπ) (Gπ) (Jπ) f

theorem chevalleyQPiForwardCounitLeg_x_heq {a b : Aπ} (f : a ⟶ b) :
    HEq ((chevalleyQPiForwardCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      ((Eπ).x ((Fπ).map f)) := by
  rw [chevalleyQPiForwardCounitLeg_eq]
  exact LeftZigzag.counitLeg_x (Fπ) (Gπ) (Eπ) f
end OddMath.SKM

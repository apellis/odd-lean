/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTransposeDenominatorUnits
import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso
import StringDiagrams.Super.PiTwo

/-! # Literal full-ELV source norms for the mixed mate

Precompose the actual reservoir restriction by E followed by the prescribed
content parity shift of H. The probe and transposed dots are exactly the
mixedPostSourcePreDot and mixedPostSourcePostDot operators, using strict
Π-SCat whiskering. No complete factor family is assumed or replaced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u

local instance elvSourceHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The twice-whiskered probe dot is the literal source pre dot. -/
theorem elvMixedSourceProbeDot_eq (xDot : End E) :
    elvRestrictionProbeDot D Sc cutoff bound i Λ h
        (E ≫ (SKM.homParityShift (k := k) κ).obj H)
        (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) =
      SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot := rfl

/-- The precomposed chosen transpose is the literal source post dot. -/
theorem elvMixedSourceTransposeDot_eq :
    elvPostTransposeDot D Sc cutoff bound i Λ h
        (E ≫ (SKM.homParityShift (k := k) κ).obj H) =
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) := rfl

/-- The even source difference is a unit at every original weight. -/
theorem elvMixedSource_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (xDot : End E) (hx : xDot ∈ parity (R := k) _ _ 0) (hu : IsUnit xDot) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h)) := by
  have hx' := Superfunctor.whiskerRight_mem hx ((SKM.homParityShift (k := k) κ).obj H)
  have hu' : IsUnit (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) :=
    hu.map ((SKM.homPost (k := k) ((SKM.homParityShift (k := k) κ).obj H)).mapEnd E)
  have hh := elvRestrictionProbe_difference_isUnit D Sc cutoff bound i Λ h
    (E ≫ (SKM.homParityShift (k := k) κ).obj H) sy hc hi
    (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) hx' hu'
  rw [elvMixedSourceTransposeDot_eq D Sc cutoff bound i Λ h E κ H,
    elvMixedSourceProbeDot_eq D Sc cutoff bound i Λ h E κ H xDot] at hh
  simpa only [neg_sub] using hh.neg

/-- The odd source square difference is a unit without a whole-fibre exponent. -/
theorem elvMixedSource_square_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (xDot : End E) (hx : xDot ∈ parity (R := k) _ _ 1) (hu : IsUnit xDot) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot ^ 2 -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  have hx' := Superfunctor.whiskerRight_mem hx ((SKM.homParityShift (k := k) κ).obj H)
  have hu' : IsUnit (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) :=
    hu.map ((SKM.homPost (k := k) ((SKM.homParityShift (k := k) κ).obj H)).mapEnd E)
  have hh := elvRestrictionProbe_square_difference_isUnit D Sc cutoff bound i Λ h
    (E ≫ (SKM.homParityShift (k := k) κ).obj H) sy hc hi
    (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) hx' hu'
  rw [elvMixedSourceProbeDot_eq D Sc cutoff bound i Λ h E κ H xDot,
    elvMixedSourceTransposeDot_eq D Sc cutoff bound i Λ h E κ H] at hh
  exact hh

/-- The companion odd source square sum is a unit with the same literal maps. -/
theorem elvMixedSource_square_sum_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (xDot : End E) (hx : xDot ∈ parity (R := k) _ _ 1) (hu : IsUnit xDot) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot ^ 2 +
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  have hx' := Superfunctor.whiskerRight_mem hx ((SKM.homParityShift (k := k) κ).obj H)
  have hu' : IsUnit (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) :=
    hu.map ((SKM.homPost (k := k) ((SKM.homParityShift (k := k) κ).obj H)).mapEnd E)
  have hh := elvRestrictionProbe_square_sum_isUnit D Sc cutoff bound i Λ h
    (E ≫ (SKM.homParityShift (k := k) κ).obj H) sy hc hi
    (xDot ▷ (SKM.homParityShift (k := k) κ).obj H) hx' hu'
  rw [elvMixedSourceProbeDot_eq D Sc cutoff bound i Λ h E κ H xDot,
    elvMixedSourceTransposeDot_eq D Sc cutoff bound i Λ h E κ H] at hh
  exact hh

end OddMath.QuiverHecke.ELVOld

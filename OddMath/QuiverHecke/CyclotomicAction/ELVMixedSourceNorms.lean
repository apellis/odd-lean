/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTransposeDenominatorUnits
import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso
import StringDiagrams.Super.PiTwo

/-! # Literal full-ELV source operators and even mixed-mate norm

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

private theorem sourcePostDot_assoc {k : Type u} [CommRing k]
    {A B C D : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (K : B ⟶ C)
    (F : C ⟶ D) (t : End F) :
    Superfunctor.whiskerLeft (E ≫ K) t =
      Superfunctor.whiskerLeft E (Superfunctor.whiskerLeft K t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The twice-whiskered probe dot is the literal source pre dot. -/
theorem elvMixedSourceProbeDot_eq (xDot : End E) :
    elvRestrictionProbeDot D Sc cutoff bound i Λ h
        (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)
        (xDot ▷ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) =
      SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot := rfl

/-- The precomposed chosen transpose is the literal source post dot. -/
theorem elvMixedSourceTransposeDot_eq :
    elvPostTransposeDot D Sc cutoff bound i Λ h
        (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) =
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) := by
  unfold elvPostTransposeDot SKM.mixedPostSourcePostDot elvActionDotTranspose
  exact sourcePostDot_assoc E
    ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)
    (elvF D Sc cutoff bound i Λ h)
    (SKM.SuperAdjunction.rightTranspose
      (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionDot D Sc cutoff bound i Λ h))

/-- The even source difference is a unit at every original weight. -/
theorem elvMixedSource_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 0)
    (xDot : End E) (hx : xDot ∈ parity (R := k) _ _ 0) (hu : IsUnit xDot) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h)) := by
  have hx' := Superfunctor.whiskerRight_mem hx ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)
  have hu' : IsUnit (show End (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) from
      xDot ▷ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) :=
    hu.map ((SKM.homPost (k := k) ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)).mapEnd E)
  have hh := elvRestrictionProbe_difference_isUnit D Sc cutoff bound i Λ h
    (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) hdot hi
    (xDot ▷ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) hx' hu'
  rw [elvMixedSourceTransposeDot_eq D Sc cutoff bound i Λ h E κ H,
    elvMixedSourceProbeDot_eq D Sc cutoff bound i Λ h E κ H xDot] at hh
  simpa only [neg_sub] using hh.neg

end OddMath.QuiverHecke.ELVOld

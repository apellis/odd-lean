/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDenominatorUnits
import OddMath.SKM.RouquierHomPostPowers
import StringDiagrams.Super.PiTwo

/-! # Denominator units on the actual content-shifted Hom summand

Use the same canonical homPiLeft structure as the existing swapped Hom
construction. The chosen normalized postdot is mapped through the actual
homParityShift functor, exactly as in homContentPostDot. Every unit is
transported through this functor; no alternative action or dot gauge is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u

local instance piSCatHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A : PiSCat.{u, u, u + 1} k} (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)

/-- The literal postcomposition image of the probe-precomposition dot. -/
abbrev elvPostProbeDot (α : End F) : End (elvPostInduction D Sc cutoff bound i Λ h F) :=
  Superfunctor.whiskerRight α (elvE D Sc cutoff bound i Λ h)

theorem elvPostProbeDot_isUnit (α : End F) (hu : IsUnit α) :
    IsUnit (elvPostProbeDot D Sc cutoff bound i Λ h F α) :=
  hu.map ((SKM.homPost (k := k) (a := A) (elvE D Sc cutoff bound i Λ h)).mapEnd F)

theorem elvPostProbeDot_mem {p : ZMod 2} (α : End F)
    (hα : α ∈ parity (R := k) _ _ p) :
    elvPostProbeDot D Sc cutoff bound i Λ h F α ∈ parity (R := k) _ _ p :=
  Superfunctor.whiskerRight_mem hα (elvE D Sc cutoff bound i Λ h)

private theorem elvPostProbe_even_comm (α : End F) (M : A) (δ : WeightBlocks D Λ y) :
    Commute
      (elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostDot D Sc cutoff bound i Λ h F) 0 M δ)
      (elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) 0 M δ) := by
  change
    ((elvE D Sc cutoff bound i Λ h).map (α.app 0 M)) δ ≫
        (elvActionDot D Sc cutoff bound i Λ h).app 0 (F.obj M) δ =
      (elvActionDot D Sc cutoff bound i Λ h).app 0 (F.obj M) δ ≫
        ((elvE D Sc cutoff bound i Λ h).map (α.app 0 M)) δ
  have hh := (elvActionDot D Sc cutoff bound i Λ h).naturality
    0 (α.app 0 M) (α.app_mem 0 M)
  simp only [koszulSign_zero_left, one_smul] at hh
  exact congrArg (fun f => f δ) hh

private theorem elvPostProbe_odd_anticomm (α : End F) (M : A) (δ : WeightBlocks D Λ y) :
    elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ *
      elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) 1 M δ =
    -(elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) 1 M δ *
      elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ) := by
  change
    ((elvE D Sc cutoff bound i Λ h).map (α.app 1 M)) δ ≫
        (elvActionDot D Sc cutoff bound i Λ h).app 1 (F.obj M) δ =
      -((elvActionDot D Sc cutoff bound i Λ h).app 1 (F.obj M) δ ≫
        ((elvE D Sc cutoff bound i Λ h).map (α.app 1 M)) δ)
  have hh := (elvActionDot D Sc cutoff bound i Λ h).naturality
    1 (α.app 1 M) (α.app_mem 1 M)
  have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
  rw [hs, neg_one_zsmul] at hh
  exact congrArg (fun f => f δ) hh

theorem elvPostProbe_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (α : End F) (hα : α ∈ parity (R := k) _ _ 0) (hu : IsUnit α) :
    IsUnit (elvPostDot D Sc cutoff bound i Λ h F -
      elvPostProbeDot D Sc cutoff bound i Λ h F α) :=
  elvPostDot_difference_isUnit D Sc cutoff bound sy hc i Λ h F hi _
    (elvPostProbeDot_mem D Sc cutoff bound i Λ h F α hα)
    (elvPostProbeDot_isUnit D Sc cutoff bound i Λ h F α hu)
    (elvPostProbe_even_comm D Sc cutoff bound i Λ h F α)

theorem elvPostProbe_square_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (α : End F) (hα : α ∈ parity (R := k) _ _ 1) (hu : IsUnit α) :
    IsUnit (elvPostProbeDot D Sc cutoff bound i Λ h F α ^ 2 -
      elvPostDot D Sc cutoff bound i Λ h F ^ 2) :=
  elvPostDot_square_difference_isUnit D Sc cutoff bound sy hc i Λ h F hi _
    (elvPostProbeDot_mem D Sc cutoff bound i Λ h F α hα)
    (elvPostProbeDot_isUnit D Sc cutoff bound i Λ h F α hu)
    (elvPostProbe_odd_anticomm D Sc cutoff bound i Λ h F α)

private theorem functor_map_end_pow {C C' : Type*} [Category C] [Category C']
    (G : C ⥤ C') (M : C) (f : End M) (n : ℕ) :
    G.map (f ^ n) = (show End (G.obj M) from G.map f) ^ n :=
  (G.mapEnd M).map_pow f n

abbrev elvShiftedPostInduction (κ : ZMod 2) :
    A ⟶ elvWeightSpace D Sc cutoff bound Λ y :=
  (SKM.homParityShift (k := k) (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj
    (elvPostInduction D Sc cutoff bound i Λ h F)

abbrev elvShiftedPostEnd
    (g : End (elvPostInduction D Sc cutoff bound i Λ h F)) (κ : ZMod 2) :
    End (elvShiftedPostInduction D Sc cutoff bound i Λ h F κ) :=
  (SKM.homParityShift (k := k) (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).map g

/-- This is the literal homContentPostDot formula for the chosen full-ELV dot. -/
abbrev elvShiftedPostDot (κ : ZMod 2) :
    End (elvShiftedPostInduction D Sc cutoff bound i Λ h F κ) :=
  elvShiftedPostEnd D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) κ

theorem elvShiftedPostProbe_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (κ : ZMod 2)
    (hi : D.parity i = 0) (α : End F)
    (hα : α ∈ parity (R := k) _ _ 0) (hu : IsUnit α) :
    IsUnit (elvShiftedPostDot D Sc cutoff bound i Λ h F κ -
      elvShiftedPostEnd D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) κ) := by
  let S := SKM.homParityShift (k := k)
    (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ
  have hh := (elvPostProbe_difference_isUnit D Sc cutoff bound i Λ h F sy hc hi α hα hu).map
    (S.mapEnd (elvPostInduction D Sc cutoff bound i Λ h F))
  change IsUnit (show End (S.obj (elvPostInduction D Sc cutoff bound i Λ h F)) from
    S.map (elvPostDot D Sc cutoff bound i Λ h F -
      elvPostProbeDot D Sc cutoff bound i Λ h F α)) at hh
  rw [Functor.map_sub] at hh
  exact hh

theorem elvShiftedPostProbe_square_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (κ : ZMod 2)
    (hi : D.parity i = 1) (α : End F)
    (hα : α ∈ parity (R := k) _ _ 1) (hu : IsUnit α) :
    IsUnit (elvShiftedPostEnd D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) κ ^ 2 -
      elvShiftedPostDot D Sc cutoff bound i Λ h F κ ^ 2) := by
  let S := SKM.homParityShift (k := k)
    (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ
  have hh := (elvPostProbe_square_difference_isUnit D Sc cutoff bound i Λ h F sy hc hi α hα hu).map
    (S.mapEnd (elvPostInduction D Sc cutoff bound i Λ h F))
  change IsUnit (show End (S.obj (elvPostInduction D Sc cutoff bound i Λ h F)) from
    S.map (elvPostProbeDot D Sc cutoff bound i Λ h F α ^ 2 -
      elvPostDot D Sc cutoff bound i Λ h F ^ 2)) at hh
  rw [Functor.map_sub, functor_map_end_pow, functor_map_end_pow] at hh
  exact hh

end OddMath.QuiverHecke.ELVOld

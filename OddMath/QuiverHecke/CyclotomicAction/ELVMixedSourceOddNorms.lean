/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceNorms

/-! # Odd mixed-source norms on the literal parenthesization

Work on E followed by (ΠH followed by actual restriction). Componentwise
nilpotence of the chosen transpose gives both source norm units without
transporting a norm through an equality of functor parenthesizations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly OddMath.QuiverHecke.CyclotomicAction
universe u v w v' w'
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X)

/-- Use the bicategory's original Hom data rather than the strict-category Quiver path. -/
local instance elvOddPiQuiver : Quiver.{u + 1} (PiSCat.{u, u, u + 1} k) :=
  (PiSCat.instBicategoryStruct (R := k)).toCategoryStruct.toQuiver

local instance elvOddPiCategoryStruct :
    CategoryStruct.{u + 1} (PiSCat.{u, u, u + 1} k) :=
  (PiSCat.instBicategoryStruct (R := k)).toCategoryStruct

/-- Fix the bundled Hom category before inserting actual coend endomorphisms. -/
local instance elvOddHomCategory (A B : PiSCat.{u, u, u + 1} k) :
    Category.{u + 1} (A ⟶ B) :=
  BicategoryStruct.homCategory A B

section Norms
variable {A B : PiSCat.{u, u, u + 1} k}

private theorem oddEndNorms
    (U : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)
    (X Y : End U) (hx : X ∈ parity (R := k) _ _ 1)
    (hy : Y ∈ parity (R := k) _ _ 1) (hu : IsUnit X)
    (hn : ∀ (M : A.carrier) (δ : WeightBlocks D Λ x), IsNilpotent
      (show End ((U.obj M) δ) from Y.app 1 M δ))
    (ha : ∀ (M : A.carrier) (δ : WeightBlocks D Λ x),
      (show End ((U.obj M) δ) from Y.app 1 M δ) *
        (show End ((U.obj M) δ) from X.app 1 M δ) =
        -((show End ((U.obj M) δ) from X.app 1 M δ) *
          (show End ((U.obj M) δ) from Y.app 1 M δ))) :
    IsUnit (X ^ 2 - Y ^ 2) ∧ IsUnit (X ^ 2 + Y ^ 2) := by
  constructor
  · apply superfunctorEnd_isUnit
    · simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
        Submodule.sub_mem _ (comp_mem hx hx) (comp_mem hy hy)
    · intro M
      change IsUnit ((show End (U.obj M) from (X ^ 2).app 0 M) -
        (show End (U.obj M) from (Y ^ 2).app 0 M))
      rw [superfunctor_odd_square_app_zero _ X hx M,
        superfunctor_odd_square_app_zero _ Y hy M]
      exact product_square_difference_isUnit
        (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
        (U.obj M) (show End (U.obj M) from X.app 1 M)
        (show End (U.obj M) from Y.app 1 M)
        (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 1 hx M δ)
        (hn M) (ha M)
  · apply superfunctorEnd_isUnit
    · simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
        Submodule.add_mem _ (comp_mem hx hx) (comp_mem hy hy)
    · intro M
      change IsUnit ((show End (U.obj M) from (X ^ 2).app 0 M) +
        (show End (U.obj M) from (Y ^ 2).app 0 M))
      rw [superfunctor_odd_square_app_zero _ X hx M,
        superfunctor_odd_square_app_zero _ Y hy M]
      exact product_square_sum_isUnit
        (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
        (U.obj M) (show End (U.obj M) from X.app 1 M)
        (show End (U.obj M) from Y.app 1 M)
        (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 1 hx M δ)
        (hn M) (ha M)

/-- Odd composition norms from the componentwise bounds of an arbitrary module-valued functor. -/
theorem mixedOddNorms (E : A ⟶ B)
    (K : B ⟶ elvWeightSpace D Sc cutoff bound Λ x)
    (a : End E) (t : End K) (ht : t ∈ parity (R := k) _ _ 1)
    (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a)
    (hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x), IsNilpotent (show End ((K.obj M) δ) from t.app 1 M δ)) :
    IsUnit ((show End (E ≫ K) from a ▷ K) ^ 2 -
      (show End (E ≫ K) from E ◁ t) ^ 2) ∧
    IsUnit ((show End (E ≫ K) from a ▷ K) ^ 2 +
      (show End (E ≫ K) from E ◁ t) ^ 2) := by
  apply oddEndNorms (A := A) D Sc cutoff bound Λ x (E ≫ K)
    (a ▷ K) (E ◁ t)
    (Superfunctor.whiskerRight_mem ha K) (Superfunctor.whiskerLeft_mem E ht)
    (hu.map ((SKM.homPost (k := k) (B := PiSCat.{u, u, u + 1} k)
      (a := A) (b := B) (c := elvWeightSpace D Sc cutoff bound Λ x) K).mapEnd E))
  · intro M δ
    exact hn (E.obj M) δ
  · intro M δ
    change K.map (a.app 1 M) δ ≫ t.app 1 (E.obj M) δ =
      -(t.app 1 (E.obj M) δ ≫ K.map (a.app 1 M) δ)
    have h := t.naturality 1 (a.app 1 M) (a.app_mem 1 M)
    have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
    rw [hs, neg_one_zsmul] at h
    exact congrArg (fun f => f δ) h

end Norms

local instance elvOddSourceHomPi (A B : PiSCat.{u, u, u + 1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

variable (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

private theorem elvMixedSource_oddNorms [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) ∧
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 +
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  let K : B ⟶ elvWeightSpace D Sc cutoff bound Λ y := (SKM.homParityShift (k := k)
    (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H
  let F : B ⟶ elvWeightSpace D Sc cutoff bound Λ x := K ≫ elvF D Sc cutoff bound i Λ h
  let t : End F := K ◁ elvActionDotTranspose D Sc cutoff bound i Λ h
  have ht : t ∈ parity (R := k) _ _ 1 :=
    Superfunctor.whiskerLeft_mem K (hi ▸ elvActionDotTranspose_mem D Sc cutoff bound i Λ h)
  have hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x), IsNilpotent (show End ((F.obj M) δ) from t.app 1 M δ) := by
    intro M δ
    obtain ⟨n, _, hn⟩ :=
      elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h hdot δ
    refine ⟨n, ?_⟩
    change (show End (((elvF D Sc cutoff bound i Λ h).obj (K.obj M)) δ) from
      (elvActionDotTranspose D Sc cutoff bound i Λ h).app 1 (K.obj M) δ) ^ n = 0
    simpa only [hi] using hn (K.obj M)
  have hh := mixedOddNorms (A := A) (B := B) D Sc cutoff bound Λ x E F a t ht ha hu hn
  set_option backward.dsimp.instances true in
    dsimp only [K, F, t] at hh
  delta elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory
    SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot elvActionDotTranspose at hh ⊢
  exact hh

/-- The literal odd source square difference is a unit without a whole-fibre exponent. -/
theorem elvMixedSource_square_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  have hh := elvMixedSource_oddNorms D Sc cutoff bound Λ x i h E κ H hdot hi a ha hu
  exact hh.1

/-- The literal odd source square sum is a unit without a whole-fibre exponent. -/
theorem elvMixedSource_square_sum_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 +
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  have hh := elvMixedSource_oddNorms D Sc cutoff bound Λ x i h E κ H hdot hi a ha hu
  exact hh.2

end OddMath.QuiverHecke.ELVOld

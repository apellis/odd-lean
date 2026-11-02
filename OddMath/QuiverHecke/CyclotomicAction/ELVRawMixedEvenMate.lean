/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedMate

/-! # The even dotted mate of the raw coefficient

This supplies the even raw-coefficient mate input for the distinct-colour
inverse assembly in `docs/Nondegeneracy/SwappedActionAssembly.md`, §5. Work
on the literal mixed-source parenthesization. Componentwise transpose
nilpotence gives its difference unit before specializing the generic mate
criterion, preserving the raw coefficient's Hom-shift witness.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory piSCatHomPi

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X)

private theorem evenEndNorm {A : PiSCat.{u, u, u + 1} k}
    (U : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)
    (X Y : End U) (hx : X ∈ parity (R := k) _ _ 0)
    (hy : Y ∈ parity (R := k) _ _ 0) (hu : IsUnit X)
    (hn : ∀ (M : A.carrier) (δ : WeightBlocks D Λ x), IsNilpotent
      (show End ((U.obj M) δ) from Y.app 0 M δ))
    (hc : ∀ (M : A.carrier) (δ : WeightBlocks D Λ x), Commute
      (show End ((U.obj M) δ) from Y.app 0 M δ)
      (show End ((U.obj M) δ) from X.app 0 M δ)) :
    IsUnit (X - Y) := by
  have hh : IsUnit (Y - X) := by
    apply superfunctorEnd_isUnit
    · exact Submodule.sub_mem _ hy hx
    · intro M
      change IsUnit ((show End (U.obj M) from Y.app 0 M) -
        (show End (U.obj M) from X.app 0 M))
      exact product_difference_isUnit
        (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
        (U.obj M) (show End (U.obj M) from X.app 0 M)
        (show End (U.obj M) from Y.app 0 M)
        (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 0 hx M δ)
        (hn M) (hc M)
  simpa only [neg_sub] using hh.neg

private theorem mixedEvenNorm {A B : PiSCat.{u, u, u + 1} k}
    (E : A ⟶ B) (K : B ⟶ elvWeightSpace D Sc cutoff bound Λ x)
    (a : End E) (t : End K) (ht : t ∈ parity (R := k) _ _ 0)
    (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a)
    (hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x), IsNilpotent
      (show End ((K.obj M) δ) from t.app 0 M δ)) :
    IsUnit ((show End (E ≫ K) from a ▷ K) -
      (show End (E ≫ K) from E ◁ t)) := by
  apply evenEndNorm D Sc cutoff bound Λ x (E ≫ K) (a ▷ K) (E ◁ t)
    (Superfunctor.whiskerRight_mem ha K) (Superfunctor.whiskerLeft_mem E ht)
    (hu.map ((SKM.homPost (k := k) (B := PiSCat.{u, u, u + 1} k)
      (a := A) (b := B) (c := elvWeightSpace D Sc cutoff bound Λ x) K).mapEnd E))
  · intro M δ
    exact hn (E.obj M) δ
  · intro M δ
    change K.map (a.app 0 M) δ ≫ t.app 0 (E.obj M) δ =
      t.app 0 (E.obj M) δ ≫ K.map (a.app 0 M) δ
    have hh := t.naturality 0 (a.app 0 M) (a.app_mem 0 M)
    simp only [koszulSign_zero_left, one_smul] at hh
    exact congrArg (fun f => f δ) hh

variable (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The literal even source norm uses the raw coefficient's Hom-shift witness. -/
theorem elvRawMixedSource_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h)) := by
  let K : B ⟶ elvWeightSpace D Sc cutoff bound Λ y := (SKM.homParityShift (k := k)
    (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H
  let F : B ⟶ elvWeightSpace D Sc cutoff bound Λ x := K ≫ elvF D Sc cutoff bound i Λ h
  let t : End F := K ◁ elvActionDotTranspose D Sc cutoff bound i Λ h
  have ht : t ∈ parity (R := k) _ _ 0 :=
    Superfunctor.whiskerLeft_mem K (hi ▸ elvActionDotTranspose_mem D Sc cutoff bound i Λ h)
  have hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x),
      IsNilpotent (show End ((F.obj M) δ) from t.app 0 M δ) := by
    intro M δ
    obtain ⟨n, _, hn⟩ :=
      elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h sy hc δ
    refine ⟨n, ?_⟩
    change (show End (((elvF D Sc cutoff bound i Λ h).obj (K.obj M)) δ) from
      (elvActionDotTranspose D Sc cutoff bound i Λ h).app 0 (K.obj M) δ) ^ n = 0
    simpa only [hi] using hn (K.obj M)
  have hh := mixedEvenNorm D Sc cutoff bound Λ x E F a t ht (hi ▸ ha) hu hn
  set_option backward.dsimp.instances true in
    dsimp only [K, F, t] at hh
  delta elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory
    SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot elvActionDotTranspose at hh ⊢
  exact hh

/-- The raw arbitrary-Z even coefficient has invertible prescribed dotted mate. -/
theorem elvRawMixedEvenMateDot_isIso [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    IsIso (SKM.homDistinctMixedInverseMateDot
      (C := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y)
      E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H
      (elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ
        ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
        sy hc a ha hu)) := by
  have hs := elvRawMixedSource_difference_isUnit D Sc cutoff bound Λ x i h E κ H sy hc hi a ha hu
  have he := elvRawMixedCoefficient_even_identities D Sc cutoff bound Λ x i h E τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
    sy hc hi a ha hu
  exact SKM.homDistinctMixedMateDot_isIso_of_inverse_units
    (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
    (c := elvWeightSpace D Sc cutoff bound Λ x)
    (d := elvWeightSpace D Sc cutoff bound Λ y)
    E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H (hi ▸ ha)
    (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h) _ he.1 he.2 hs

end OddMath.QuiverHecke.ELVOld

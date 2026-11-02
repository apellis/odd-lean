/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedCoefficient

/-! # The odd dotted mate of the raw arbitrary-input coefficient

This supplies the raw-coefficient mate input needed by the distinct-colour
inverse assembly in `docs/Nondegeneracy/SwappedActionAssembly.md`, §5. All Hom
parity shifts use the existing post-induction witness, so the coefficient is
literally the one constructed for arbitrary Z before its mate specialization.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory piSCatHomPi
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- Both literal source norms use the same Hom-shift witness as the raw coefficient. -/
theorem elvRawMixedSource_oddNorms [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
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
  have hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x),
      IsNilpotent (show End ((F.obj M) δ) from t.app 1 M δ) := by
    intro M δ
    obtain ⟨n, _, hn⟩ :=
      elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h sy hc δ
    refine ⟨n, ?_⟩
    change (show End (((elvF D Sc cutoff bound i Λ h).obj (K.obj M)) δ) from
      (elvActionDotTranspose D Sc cutoff bound i Λ h).app 1 (K.obj M) δ) ^ n = 0
    simpa only [hi] using hn (K.obj M)
  have hh := mixedOddNorms (A := A) (B := B) D Sc cutoff bound Λ x E F a t ht (hi ▸ ha) hu hn
  set_option backward.dsimp.instances true in
    dsimp only [K, F, t] at hh
  delta elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory
    SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot elvActionDotTranspose at hh ⊢
  exact hh

/-- The raw arbitrary-Z odd coefficient has invertible prescribed dotted mate. -/
theorem elvRawMixedOddMateDot_isIso [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    IsIso (SKM.homDistinctMixedInverseMateDot
      (C := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y)
      E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H
      (elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ
        ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
        sy hc a ha hu)) := by
  have hs := elvRawMixedSource_oddNorms D Sc cutoff bound Λ x i h E κ H sy hc hi a ha hu
  have ht := elvRawMixed_square_difference_isUnit D Sc cutoff bound Λ x i h E τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
    sy hc hi a (hi ▸ ha) hu
  have he := elvRawMixedCoefficient_odd_identities D Sc cutoff bound Λ x i h E τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
    sy hc hi a ha hu
  exact SKM.homDistinctMixedMateDot_isIso_of_inverse_odd_units
    (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
    (c := elvWeightSpace D Sc cutoff bound Λ x)
    (d := elvWeightSpace D Sc cutoff bound Λ y)
    E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H (hi ▸ ha)
    (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h) ht hs.1 hs.2 _ he.2

end OddMath.QuiverHecke.ELVOld

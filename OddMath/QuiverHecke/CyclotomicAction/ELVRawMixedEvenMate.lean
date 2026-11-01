/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedMate

/-! # The even dotted mate of the raw coefficient

This is the even raw-coefficient mate input for the distinct-colour inverse
assembly in docs/Nondegeneracy/SwappedActionAssembly.md, §5. The actual
coefficient, chosen transpose and Hom-shift witness remain unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory piSCatHomPi

private theorem sourceNorm_reassoc {k : Type u} [CommRing k]
    {A B C Q : PiSCat.{u, u, u + 1} k}
    (E : A ⟶ B) (K : B ⟶ C) (F : C ⟶ Q) (a : End E) (t : End F)
    (hu : IsUnit (show End ((E ≫ K) ≫ F) from ((a ▷ K) ▷ F) - (E ≫ K) ◁ t)) :
    IsUnit (show End (E ≫ (K ≫ F)) from a ▷ (K ≫ F) - E ◁ (K ◁ t)) :=
  hu

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
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
  have hx := Superfunctor.whiskerRight_mem (hi ▸ ha) K
  have hv : IsUnit (show End (E ≫ K) from a ▷ K) :=
    hu.map ((SKM.homPost (k := k) (B := PiSCat.{u, u, u + 1} k)
      (a := A) (b := B) (c := elvWeightSpace D Sc cutoff bound Λ y) K).mapEnd E)
  have hh := elvRestrictionProbe_difference_isUnit D Sc cutoff bound i Λ h (E ≫ K)
    sy hc hi (a ▷ K) hx hv
  have hh' := sourceNorm_reassoc E K (elvF D Sc cutoff bound i Λ h) a
    (elvActionDotTranspose D Sc cutoff bound i Λ h)
    (by simpa only [elvPostTransposeDot, elvRestrictionProbeDot, neg_sub] using hh.neg)
  set_option backward.dsimp.instances true in
    dsimp only [K] at hh'
  delta SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot elvActionDotTranspose at hh' ⊢
  exact hh'

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

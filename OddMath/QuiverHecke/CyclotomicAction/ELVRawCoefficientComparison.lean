/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedEvenMate

/-! # Identifying the raw coefficient by its prescribed identities

The literal coefficient comparison required by
`docs/Nondegeneracy/SwappedActionAssembly.md`, §2 (A6), uses uniqueness
under the existing denominator units. In particular the numerator-first
raw odd coefficient agrees with the inverse-first crossing formula.
The arbitrary pre-induction functor and chosen Hom shifts are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory piSCatHomPi

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (τ : ZMod 2)
  (Z : B ⟶ elvWeightSpace D Sc cutoff bound Λ x)

/-- One prescribed even identity identifies a coefficient on any raw input. -/
theorem elvRawMixedCoefficient_eq_of_even_identity [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a)
    (α : End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z))
    (hα : α ≫ (elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z -
      elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a) = 𝟙 _) :
    α = elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ Z sy hc a ha hu := by
  have hd := elvRawMixed_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a (hi ▸ ha) hu
  have he := elvRawMixedCoefficient_even_identities D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a ha hu
  exact hd.mul_left_cancel (hα.trans he.1.symm)

/-- One prescribed odd identity identifies a coefficient on any raw input. -/
theorem elvRawMixedCoefficient_eq_of_odd_identity [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a)
    (α : End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z))
    (hα : α ≫
        (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a ≫
          elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a -
        elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z ≫
          elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z) =
      elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a -
        elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z) :
    α = elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ Z sy hc a ha hu := by
  have hd := elvRawMixed_square_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a (hi ▸ ha) hu
  have he := elvRawMixedCoefficient_odd_identities D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a ha hu
  apply hd.mul_left_cancel
  simpa only [pow_two, End.mul_def] using hα.trans he.1.symm

/-- The raw odd coefficient is the inverse-first formula used by CrossCoeff. -/
theorem elvRawMixedCoefficient_odd_inverseFirst [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ Z sy hc a ha hu =
      ↑((elvRawMixed_square_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
        sy hc hi a (hi ▸ ha) hu).unit⁻¹) *
        (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a -
          elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z) := by
  apply Eq.symm
  apply elvRawMixedCoefficient_eq_of_odd_identity D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a ha hu
  let U := elvRawMixed_square_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a (hi ▸ ha) hu
  have hh :
      (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a ^ 2 -
        elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z ^ 2) * ↑(U.unit⁻¹) =
      (1 : End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z)) := by
    simpa only [U.unit_spec] using U.unit.mul_inv
  have hp :
      (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a ^ 2 -
        elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z ^ 2) *
        (↑(U.unit⁻¹) * (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a -
          elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z)) =
      elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a -
        elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z := by
    rw [← mul_assoc, hh, one_mul]
  simpa only [pow_two, End.mul_def, U] using hp

variable (κ : ZMod 2) (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The previously constructed even mate coefficient is the raw specialization. -/
theorem elvMixedEvenCoefficient_eq_raw [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    elvMixedEvenCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a (hi ▸ ha) hu =
      elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ
        ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
        sy hc a ha hu := by
  apply elvRawMixedCoefficient_eq_of_even_identity D Sc cutoff bound Λ x i h E τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
    sy hc hi a ha hu
  exact (elvMixedEvenCoefficient_identities D Sc cutoff bound Λ x i h E κ τ H
    sy hc hi a (hi ▸ ha) hu).1

/-- The previously constructed odd mate coefficient is the raw specialization. -/
theorem elvMixedOddCoefficient_eq_raw [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a (hi ▸ ha) hu =
      elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ
        ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
        sy hc a ha hu := by
  apply elvRawMixedCoefficient_eq_of_odd_identity D Sc cutoff bound Λ x i h E τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
    sy hc hi a ha hu
  exact (elvMixedOddCoefficient_identities D Sc cutoff bound Λ x i h E κ τ H
    sy hc hi a (hi ▸ ha) hu).1

/-- Both moving parities give the dotted mate of the same raw coefficient. -/
theorem elvRawMixedMateDot_isIso [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    IsIso (SKM.homDistinctMixedInverseMateDot
      (C := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y)
      E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H
      (elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ
        ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)
        sy hc a ha hu)) := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · exact elvRawMixedEvenMateDot_isIso D Sc cutoff bound Λ x i h E κ τ H
      sy hc hi a ha hu
  · exact elvRawMixedOddMateDot_isIso D Sc cutoff bound Λ x i h E κ τ H
      sy hc hi a ha hu

end OddMath.QuiverHecke.ELVOld

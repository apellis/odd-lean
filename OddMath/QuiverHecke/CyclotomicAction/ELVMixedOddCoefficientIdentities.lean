/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedCoefficientParity
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence

/-! # Both inverse identities of the prescribed odd mixed coefficient

The odd clause of `ProbeReservoir.CrossCoeff.IsInverse`, used by the prescribed
crossing in `docs/Nondegeneracy/SwappedActionAssembly.md`, §2 (A6), needs both
orientations of the square-denominator identity. These hold for the existing
numerator-first full-ELV coefficient, by literal target-J dot anticommutation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r

private theorem oddCoefficient_other_identity {R : Type*} [Ring R]
    (X Y : R) (hu : IsUnit (X ^ 2 - Y ^ 2)) (ha : Y * X = -(X * Y)) :
    (X ^ 2 - Y ^ 2) * ((X - Y) * ↑(hu.unit⁻¹)) = X - Y := by
  have hc := OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.commute_sq_of_anticommute ha
  have hcomm : Commute (X - Y) (X ^ 2 - Y ^ 2) := by
    simp only [pow_two]
    exact (((Commute.refl X).mul_right (Commute.refl X)).sub_right hc.1).sub_left
      (hc.2.sub_right ((Commute.refl Y).mul_right (Commute.refl Y)))
  have hv : (X ^ 2 - Y ^ 2) * ↑(hu.unit⁻¹) = (1 : R) := by
    simpa only [hu.unit_spec] using hu.unit.mul_inv
  rw [← mul_assoc, ← hcomm.eq, mul_assoc, hv, mul_one]

section Generic
variable {k : Type r} [CommRing k] {C : Type u} [BicategoryStruct.{w, v} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ a b : C, Supercategory k (a ⟶ b)] [TwoSupercategory k C]
  [∀ a b : C, PiSupercategory k (a ⟶ b)]
  {a b c d : C} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (κ τ : ZMod 2) (H : b ⟶ d)

private theorem mixedJOdd_anticomm (x : End E) (y : End E')
    (hx : x ∈ parity (R := k) _ _ 1) (hy : y ∈ parity (R := k) _ _ 1) :
    SKM.mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
      SKM.mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x =
      -(SKM.mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        SKM.mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
  have h := SKM.homMixedInterchange_dot_exchange (k := k) E E' τ
    ((SKM.homParityShift (k := k) κ).obj H ≫ F') x y hx hy
  have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
  rw [hs, neg_one_zsmul] at h
  exact h

end Generic

attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct
  elvOddHomCategory elvOddSourceHomPi
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The odd coefficient also satisfies the opposite denominator identity. -/
theorem elvMixedOddCoefficient_comp_square_difference [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu ≫
      (SKM.mixedPostJPreDot (k := k) E κ τ H
          (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a ≫
        SKM.mixedPostJPreDot (k := k) E κ τ H
          (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a -
        SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
          (elvActionDot D Sc cutoff bound i Λ h) ≫
        SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
          (elvActionDot D Sc cutoff bound i Λ h)) =
      SKM.mixedPostJPreDot (k := k) E κ τ H
          (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a -
        SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
          (elvActionDot D Sc cutoff bound i Λ h) := by
  have hac := mixedJOdd_anticomm E κ τ H (F' := elvF D Sc cutoff bound i Λ h) a
    (elvActionDot D Sc cutoff bound i Λ h) ha (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h)
  simpa only [elvMixedOddCoefficient, pow_two, End.mul_def] using
    oddCoefficient_other_identity _ _ (elvMixedTarget_square_difference_isUnit
      D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu) hac

/-- Both odd `CrossCoeff.IsInverse` identities hold for the prescribed coefficient. -/
theorem elvMixedOddCoefficient_identities [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    let α := elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu
    let X := SKM.mixedPostJPreDot (k := k) E κ τ H
      (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a
    let Y := SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
      (elvActionDot D Sc cutoff bound i Λ h)
    α ≫ (X ≫ X - Y ≫ Y) = X - Y ∧ (X ≫ X - Y ≫ Y) ≫ α = X - Y := by
  exact ⟨elvMixedOddCoefficient_comp_square_difference
    D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu,
    elvMixedOddCoefficient_identity D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu⟩

end OddMath.QuiverHecke.ELVOld

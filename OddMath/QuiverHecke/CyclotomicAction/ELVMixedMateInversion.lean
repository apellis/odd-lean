/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceOddNorms
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedDenominatorUnits
import OddMath.SKM.RouquierHomPostInverseUnits

/-! # Prescribed inverse coefficients for the actual full-ELV mixed mate -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u v w r
variable {k : Type r} [CommRing k] {C : Type u} [BicategoryStruct.{w, v} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ a b : C, Supercategory k (a ⟶ b)] [TwoSupercategory k C]
  [∀ a b : C, PiSupercategory k (a ⟶ b)]
  {a b c d : C} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (adj : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The literal dotted mate of the prescribed inverse crossing, with its endpoints fixed. -/
def homDistinctMixedInverseMateDot
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E'))) :
    E ≫ ((homParityShift (k := k) κ).obj H ≫ F') ⟶
      (homParityShift (k := k) τ).obj (E ≫ H) ≫ F' :=
  homDistinctMixedMateDot E adj κ τ H
    ((homMixedInterchange (k := k) E E' κ τ
      ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫ (homMixedInterchange (k := k) E E' κ τ
          ((homParityShift (k := k) κ).obj H ≫ F')).inv)))

end OddMath.SKM

namespace OddMath.QuiverHecke.ELVOld
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct
  elvOddHomCategory elvOddSourceHomPi

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The literal target square denominator is a unit for the prescribed dot. -/
theorem elvMixedTarget_square_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 -
      SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  let K : B ⟶ elvWeightSpace D Sc cutoff bound Λ x :=
    (SKM.homParityShift (k := k)
      (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H ≫
      elvF D Sc cutoff bound i Λ h
  let F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x := E ≫ K
  let b : End F := a ▷ K
  have hb : b ∈ parity (R := k) _ _ 1 := Superfunctor.whiskerRight_mem ha K
  have hv : IsUnit b := hu.map ((SKM.homPost (k := k)
    (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
    (c := elvWeightSpace D Sc cutoff bound Λ x) K).mapEnd E)
  have hh := elvShiftedPostProbe_square_difference_isUnit D Sc cutoff bound i Λ h F
    sy hc τ hi b hb hv
  set_option backward.dsimp.instances true in
    dsimp only [F, b, K] at hh
  delta SKM.mixedPostJPreDot SKM.mixedPostJPostDot
    elvShiftedPostEnd elvShiftedPostDot elvPostProbeDot elvPostDot at hh ⊢
  exact hh

/-- The numerator-first coefficient from the written inverse formula. -/
def elvMixedOddCoefficient [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    End ((SKM.homParityShift (k := k) τ).obj
      ((E ≫ ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)) ≫
        elvE D Sc cutoff bound i Λ h)) :=
  (SKM.mixedPostJPreDot (k := k) E κ τ H
      (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a -
    SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
      (elvActionDot D Sc cutoff bound i Λ h)) *
    ↑((elvMixedTarget_square_difference_isUnit D Sc cutoff bound Λ x i h E κ τ H
      sy hc hi a ha hu).unit⁻¹)

private theorem oddCoefficient_identity {R : Type*} [Ring R]
    (X Y : R) (hu : IsUnit (X ^ 2 - Y ^ 2)) :
    ((X - Y) * ↑(hu.unit⁻¹)) * (X ^ 2 - Y ^ 2) = X - Y := by
  have hh : ↑(hu.unit⁻¹) * (X ^ 2 - Y ^ 2) = (1 : R) := by
    simpa only [hu.unit_spec] using hu.unit.inv_mul
  rw [mul_assoc, hh, mul_one]

/-- The actual coefficient satisfies the prescribed square-denominator identity. -/
theorem elvMixedOddCoefficient_identity [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    (SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a ≫
      SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a -
      SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ≫
      SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h)) ≫
      elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu =
    SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a -
      SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) := by
  simpa only [elvMixedOddCoefficient, pow_two, End.mul_def] using
    oddCoefficient_identity _ _ (elvMixedTarget_square_difference_isUnit
      D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)

/-- The dotted mate of the prescribed odd crossing is invertible on the actual ELV action. -/
theorem elvMixedOddMateDot_isIso [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsIso (SKM.homDistinctMixedInverseMateDot
      (C := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y)
      E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H
      (elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)) := by
  exact SKM.homDistinctMixedMateDot_isIso_of_inverse_odd_units (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y) E
    (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H ha
    (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h)
    (elvMixedTarget_square_difference_isUnit D Sc cutoff bound Λ x i h E κ τ H
      sy hc hi a ha hu)
    (elvMixedSource_square_difference_isUnit D Sc cutoff bound Λ x i h E κ H
      sy hc hi a ha hu)
    (elvMixedSource_square_sum_isUnit D Sc cutoff bound Λ x i h E κ H
      sy hc hi a ha hu)
    (elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)
    (elvMixedOddCoefficient_identity D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)

end OddMath.QuiverHecke.ELVOld

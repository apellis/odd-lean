/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateInversion

/-! # Even inverse coefficient and dotted mate

This supplies the even inverse-coefficient step used by the mixed-mate
construction in `docs/Nondegeneracy/SwappedNondegeneracy.md`, using the chosen
full-ELV dot and adjunction and the existing probe dot unit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct
  elvOddHomCategory elvSourceHomPi

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The target-J even denominator is a unit for the chosen dot. -/
theorem elvMixedTarget_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) -
      SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a) := by
  let K : B ⟶ elvWeightSpace D Sc cutoff bound Λ x :=
    (SKM.homParityShift (k := k)
      (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H ≫
      elvF D Sc cutoff bound i Λ h
  let F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x := E ≫ K
  let b : End F := a ▷ K
  have hb : b ∈ parity (R := k) _ _ 0 := Superfunctor.whiskerRight_mem ha K
  have hv : IsUnit b := hu.map ((SKM.homPost (k := k)
    (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
    (c := elvWeightSpace D Sc cutoff bound Λ x) K).mapEnd E)
  have hh := elvShiftedPostProbe_difference_isUnit D Sc cutoff bound i Λ h F
    sy hc τ hi b hb hv
  set_option backward.dsimp.instances true in
    dsimp only [F, b, K] at hh
  delta SKM.mixedPostJPreDot SKM.mixedPostJPostDot
    elvShiftedPostEnd elvShiftedPostDot elvPostProbeDot elvPostDot at hh ⊢
  exact hh

/-- The prescribed even coefficient is the inverse of the target difference. -/
def elvMixedEvenCoefficient [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    End ((SKM.homParityShift (k := k) τ).obj
      ((E ≫ ((SKM.homParityShift (k := k) κ).obj H ≫ elvF D Sc cutoff bound i Λ h)) ≫
        elvE D Sc cutoff bound i Λ h)) :=
  ↑((elvMixedTarget_difference_isUnit D Sc cutoff bound Λ x i h E κ τ H
    sy hc hi a ha hu).unit⁻¹)

private theorem unit_inverse_comp_left {C : Type*} [Category C]
    {M : C} (f : End M) (hu : IsUnit f) : (↑(hu.unit⁻¹) : End M) ≫ f = 𝟙 M := by
  simpa only [hu.unit_spec, End.mul_def, End.one_def] using hu.unit.mul_inv

private theorem unit_inverse_comp_right {C : Type*} [Category C]
    {M : C} (f : End M) (hu : IsUnit f) : f ≫ (↑(hu.unit⁻¹) : End M) = 𝟙 M := by
  simpa only [hu.unit_spec, End.mul_def, End.one_def] using hu.unit.inv_mul

/-- Both prescribed inverse identities hold for the even coefficient. -/
theorem elvMixedEvenCoefficient_identities [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    let α := elvMixedEvenCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu
    let δ := SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
      (elvActionDot D Sc cutoff bound i Λ h) -
      SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a
    α ≫ δ = 𝟙 _ ∧ δ ≫ α = 𝟙 _ := by
  exact ⟨unit_inverse_comp_left _ (elvMixedTarget_difference_isUnit
    D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu),
    unit_inverse_comp_right _ (elvMixedTarget_difference_isUnit
      D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)⟩

/-- The dotted mate of the prescribed even crossing is invertible. -/
theorem elvMixedEvenMateDot_isIso [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    IsIso (SKM.homDistinctMixedInverseMateDot
      (C := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
      (c := elvWeightSpace D Sc cutoff bound Λ x)
      (d := elvWeightSpace D Sc cutoff bound Λ y)
      E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H
      (elvMixedEvenCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)) := by
  have hs := elvMixedSource_difference_isUnit D Sc cutoff bound i Λ h E κ H sy hc hi a ha hu
  have hh := elvMixedEvenCoefficient_identities D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu
  exact SKM.homDistinctMixedMateDot_isIso_of_inverse_units
    (B := PiSCat.{u, u, u + 1} k) (a := A) (b := B)
    (c := elvWeightSpace D Sc cutoff bound Λ x)
    (d := elvWeightSpace D Sc cutoff bound Λ y)
    E (elvActionAdjunction D Sc cutoff bound i Λ h) κ τ H ha
    (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h)
    (elvMixedEvenCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu)
    hh.1 hh.2
    hs

end OddMath.QuiverHecke.ELVOld

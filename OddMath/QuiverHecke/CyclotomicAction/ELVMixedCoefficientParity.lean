/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedEvenMateInversion

/-! # Parity of the prescribed mixed inverse coefficients

This supplies the coefficient homogeneity needed by the prescribed mixed
crossings in `docs/Nondegeneracy/SwappedActionAssembly.md`, §2. The coefficients
are those already constructed from the chosen full-ELV dot and its norm units.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r

private theorem endUnitInverse_mem {k : Type r} [CommRing k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [Supercategory k C] {M : C} (f : End M) (hu : IsUnit f) {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) :
    (↑(hu.unit⁻¹) : End M) ∈ parity (R := k) _ _ p := by
  let e : M ≅ M := Aut.unitsEndEquivAut M hu.unit
  have he : e.hom ∈ parity (R := k) _ _ p := by
    change (↑hu.unit : End M) ∈ parity (R := k) _ _ p
    simpa only [hu.unit_spec] using hf
  exact Supercategory.inv_mem e he

section Generic
variable {k : Type r} [CommRing k] {C : Type u} [BicategoryStruct.{w, v} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ a b : C, Supercategory k (a ⟶ b)] [TwoSupercategory k C]
  [∀ a b : C, PiSupercategory k (a ⟶ b)]
  {a b c d : C} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (κ τ : ZMod 2) (H : b ⟶ d)

private theorem mixedJPreDot_mem {p : ZMod 2} (x : End E)
    (hx : x ∈ parity (R := k) _ _ p) :
    SKM.mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ∈
      parity (R := k) _ _ p :=
  map_mem (SKM.homParityShift (k := k) τ)
    (TwoSupercategory.whiskerRight_mem E'
      (TwoSupercategory.whiskerRight_mem ((SKM.homParityShift (k := k) κ).obj H ≫ F') hx))

private theorem mixedJPostDot_mem {p : ZMod 2} (y : End E')
    (hy : y ∈ parity (R := k) _ _ p) :
    SKM.mixedPostJPostDot (k := k) E κ τ H (F' := F') y ∈ parity (R := k) _ _ p :=
  map_mem (SKM.homParityShift (k := k) τ)
    (TwoSupercategory.whiskerLeft_mem (E ≫ ((SKM.homParityShift (k := k) κ).obj H ≫ F')) hy)

end Generic

attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ τ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

section Odd
attribute [local instance] elvOddSourceHomPi

/-- The numerator-first odd coefficient has the moving colour's odd parity. -/
theorem elvMixedOddCoefficient_mem [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    elvMixedOddCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu ∈
      parity (R := k) _ _ 1 := by
  have hx := mixedJPreDot_mem E κ τ H (E' := elvE D Sc cutoff bound i Λ h)
    (F' := elvF D Sc cutoff bound i Λ h) a ha
  have hy := mixedJPostDot_mem E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
    (elvActionDot D Sc cutoff bound i Λ h) (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h)
  have hd := Submodule.sub_mem _ (comp_mem hx hx) (comp_mem hy hy)
  have hd' : SKM.mixedPostJPreDot (k := k) E κ τ H
        (E' := elvE D Sc cutoff bound i Λ h) (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 -
      SKM.mixedPostJPostDot (k := k) E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2 ∈ parity (R := k) _ _ 0 := by
    simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using hd
  have hh := endUnitInverse_mem _ (elvMixedTarget_square_difference_isUnit
    D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu) hd'
  simpa only [elvMixedOddCoefficient, End.mul_def, zero_add] using
    comp_mem hh (Submodule.sub_mem _ hx hy)

end Odd

section Even
attribute [local instance] elvSourceHomPi

/-- The inverse of the even target difference is even. -/
theorem elvMixedEvenCoefficient_mem [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    elvMixedEvenCoefficient D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu ∈
      parity (R := k) _ _ 0 := by
  have hx := mixedJPreDot_mem E κ τ H (E' := elvE D Sc cutoff bound i Λ h)
    (F' := elvF D Sc cutoff bound i Λ h) a ha
  have hy := mixedJPostDot_mem E κ τ H (F' := elvF D Sc cutoff bound i Λ h)
    (elvActionDot D Sc cutoff bound i Λ h) (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h)
  exact endUnitInverse_mem _ (elvMixedTarget_difference_isUnit
    D Sc cutoff bound Λ x i h E κ τ H sy hc hi a ha hu) (Submodule.sub_mem _ hy hx)

end Even
end OddMath.QuiverHecke.ELVOld

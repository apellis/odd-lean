/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedOddCoefficientIdentities

/-! # Prescribed coefficients on arbitrary pre-induction Hom objects

This supplies the raw coefficient required by `CrossCoeff.a` in
`docs/Nondegeneracy/SwappedActionAssembly.md`, §2 (A6), on the existing full-ELV
weight-module target. The input functor Z is arbitrary; it need not factor
through reservoir restriction. No full factor family is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r

private theorem rawUnitInverse_mem {k : Type r} [CommRing k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [Supercategory k C] {M : C} (f : End M) (hu : IsUnit f) {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) :
    (↑(hu.unit⁻¹) : End M) ∈ parity (R := k) _ _ p := by
  let e : M ≅ M := Aut.unitsEndEquivAut M hu.unit
  have he : e.hom ∈ parity (R := k) _ _ p := by
    change (↑hu.unit : End M) ∈ parity (R := k) _ _ p
    simpa only [hu.unit_spec] using hf
  exact Supercategory.inv_mem e he

private theorem rawOddIdentities {R : Type*} [Ring R] (X Y : R)
    (hu : IsUnit (X ^ 2 - Y ^ 2)) (ha : Y * X = -(X * Y)) :
    let α := (X - Y) * ↑(hu.unit⁻¹)
    α * (X ^ 2 - Y ^ 2) = X - Y ∧ (X ^ 2 - Y ^ 2) * α = X - Y := by
  have hc := OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.commute_sq_of_anticommute ha
  have hcomm : Commute (X - Y) (X ^ 2 - Y ^ 2) := by
    simp only [pow_two]
    exact (((Commute.refl X).mul_right (Commute.refl X)).sub_right hc.1).sub_left
      (hc.2.sub_right ((Commute.refl Y).mul_right (Commute.refl Y)))
  have hl : ↑(hu.unit⁻¹) * (X ^ 2 - Y ^ 2) = (1 : R) := by
    simpa only [hu.unit_spec] using hu.unit.inv_mul
  have hr : (X ^ 2 - Y ^ 2) * ↑(hu.unit⁻¹) = (1 : R) := by
    simpa only [hu.unit_spec] using hu.unit.mul_inv
  constructor
  · rw [mul_assoc, hl, mul_one]
  · rw [← mul_assoc, ← hcomm.eq, mul_assoc, hr, mul_one]

section Generic
variable {k : Type r} [CommRing k] {C : Type u} [BicategoryStruct.{w, v} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ a b : C, Supercategory k (a ⟶ b)] [TwoSupercategory k C]
  [∀ a b : C, PiSupercategory k (a ⟶ b)]
  {a b c d : C} (E : a ⟶ b) (G : c ⟶ d) (τ : ZMod 2) (Z : b ⟶ c)

private theorem rawDot_anticomm (x : End E) (y : End G)
    (hx : x ∈ parity (R := k) _ _ 1) (hy : y ∈ parity (R := k) _ _ 1) :
    let X : End ((SKM.homParityShift (k := k) τ).obj ((E ≫ Z) ≫ G)) :=
      (SKM.homParityShift (k := k) τ).map ((x ▷ Z) ▷ G)
    let Y : End ((SKM.homParityShift (k := k) τ).obj ((E ≫ Z) ≫ G)) :=
      (SKM.homParityShift (k := k) τ).map ((E ≫ Z) ◁ y)
    Y * X = -(X * Y) := by
  have h := SKM.homMixedInterchange_dot_exchange (k := k) E G τ Z x y hx hy
  have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
  rw [hs, neg_one_zsmul] at h
  exact h

end Generic

attribute [local instance] elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory piSCatHomPi
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (τ : ZMod 2)
  (Z : B ⟶ elvWeightSpace D Sc cutoff bound Λ x)

/-- The existing shifted post-induction object for an arbitrary input Z. -/
abbrev elvRawMixedTarget := elvShiftedPostInduction D Sc cutoff bound i Λ h (E ≫ Z) τ

/-- The literal mapped probe dot on the raw `(R,P)` target. -/
abbrev elvRawMixedPreDot (a : End E) : End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z) :=
  elvShiftedPostEnd D Sc cutoff bound i Λ h (E ≫ Z)
    (elvPostProbeDot D Sc cutoff bound i Λ h (E ≫ Z) (a ▷ Z)) τ

/-- The chosen shifted reservoir post-dot on the same target. -/
abbrev elvRawMixedPostDot : End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z) :=
  elvShiftedPostDot D Sc cutoff bound i Λ h (E ≫ Z) τ

private theorem rawPreUnit (a : End E) (hu : IsUnit a) :
    IsUnit (show End (E ≫ Z) from a ▷ Z) :=
  hu.map ((SKM.homPost (k := k) (B := PiSCat.{u, u, u + 1} k)
    (a := A) (b := B) (c := elvWeightSpace D Sc cutoff bound Λ x) Z).mapEnd E)

/-- The even denominator unit holds for every raw input functor Z. -/
theorem elvRawMixed_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 0) (hu : IsUnit a) :
    IsUnit (elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z -
      elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a) :=
  elvShiftedPostProbe_difference_isUnit D Sc cutoff bound i Λ h (E ≫ Z) sy hc τ hi
    (a ▷ Z) (Superfunctor.whiskerRight_mem ha Z) (rawPreUnit D Sc cutoff bound Λ x E Z a hu)

/-- The odd square denominator unit holds for every raw input functor Z. -/
theorem elvRawMixed_square_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a ^ 2 -
      elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z ^ 2) :=
  elvShiftedPostProbe_square_difference_isUnit D Sc cutoff bound i Λ h (E ≫ Z) sy hc τ hi
    (a ▷ Z) (Superfunctor.whiskerRight_mem ha Z) (rawPreUnit D Sc cutoff bound Λ x E Z a hu)

private theorem rawPre_mem {p : ZMod 2} (a : End E) (ha : a ∈ parity (R := k) _ _ p) :
    elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a ∈ parity (R := k) _ _ p :=
  map_mem (SKM.homParityShift (k := k) τ)
    (Superfunctor.whiskerRight_mem (Superfunctor.whiskerRight_mem ha Z)
      (elvE D Sc cutoff bound i Λ h))

private theorem rawPost_mem :
    elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z ∈ parity (R := k) _ _ (D.parity i) :=
  map_mem (SKM.homParityShift (k := k) τ)
    (Superfunctor.whiskerLeft_mem (E ≫ Z) (elvActionDot_mem D Sc cutoff bound i Λ h))

private theorem rawParity_eq_one {p : ZMod 2} (hp : p ≠ 0) : p = 1 := by
  fin_cases p
  · exact absurd rfl hp
  · rfl

/-- The prescribed raw coefficient, with no restriction-factorization premise on Z. -/
def elvRawMixedCoefficient [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z) :=
  if hi : D.parity i = 0 then
    ↑((elvRawMixed_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
      sy hc hi a (hi ▸ ha) hu).unit⁻¹)
  else
    (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a -
      elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z) *
      ↑((elvRawMixed_square_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
        sy hc (rawParity_eq_one hi) a ((rawParity_eq_one hi) ▸ ha) hu).unit⁻¹)

/-- Both even inverse identities hold on every arbitrary raw input Z. -/
theorem elvRawMixedCoefficient_even_identities [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 0)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    let α := elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ Z sy hc a ha hu
    let δ := elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z -
      elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a
    α ≫ δ = 𝟙 _ ∧ δ ≫ α = 𝟙 _ := by
  let U := elvRawMixed_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
    sy hc hi a (hi ▸ ha) hu
  have hl : (elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z -
      elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a) * ↑(U.unit⁻¹) = 1 := by
    simpa only [U.unit_spec] using U.unit.mul_inv
  have hr : (↑(U.unit⁻¹) : End (elvRawMixedTarget D Sc cutoff bound Λ x i h E τ Z)) *
      (elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z -
        elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a) = 1 := by
    simpa only [U.unit_spec] using U.unit.inv_mul
  simpa only [elvRawMixedCoefficient, dite_eq_left hi, End.mul_def, End.one_def, U] using
    And.intro hl hr

/-- Both odd square-denominator identities hold on every arbitrary raw input Z. -/
theorem elvRawMixedCoefficient_odd_identities [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    let α := elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ Z sy hc a ha hu
    let X := elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a
    let Y := elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z
    α ≫ (X ≫ X - Y ≫ Y) = X - Y ∧ (X ≫ X - Y ≫ Y) ≫ α = X - Y := by
  have hi0 : D.parity i ≠ 0 := by rw [hi]; decide
  have hac := rawDot_anticomm E (elvE D Sc cutoff bound i Λ h) τ Z a
    (elvActionDot D Sc cutoff bound i Λ h) (hi ▸ ha)
    (hi ▸ elvActionDot_mem D Sc cutoff bound i Λ h)
  have hh := rawOddIdentities
    (elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a)
    (elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z)
    (elvRawMixed_square_difference_isUnit D Sc cutoff bound Λ x i h E τ Z
      sy hc hi a (hi ▸ ha) hu) hac
  simpa only [elvRawMixedCoefficient, dite_eq_right hi0, pow_two, End.mul_def] using
    And.intro hh.2 hh.1

/-- The raw coefficient retains the moving colour's parity. -/
theorem elvRawMixedCoefficient_mem [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (a : End E) (ha : a ∈ parity (R := k) _ _ (D.parity i)) (hu : IsUnit a) :
    elvRawMixedCoefficient D Sc cutoff bound Λ x i h E τ Z sy hc a ha hu ∈
      parity (R := k) _ _ (D.parity i) := by
  by_cases hi : D.parity i = 0
  · have hh := rawUnitInverse_mem _ (elvRawMixed_difference_isUnit
      D Sc cutoff bound Λ x i h E τ Z sy hc hi a (hi ▸ ha) hu)
      (Submodule.sub_mem _ (hi ▸ rawPost_mem D Sc cutoff bound Λ x i h E τ Z)
        (rawPre_mem D Sc cutoff bound Λ x i h E τ Z a (hi ▸ ha)))
    rw [elvRawMixedCoefficient, dite_eq_left hi]
    simpa only [hi] using hh
  · have hi1 := rawParity_eq_one hi
    have hx := rawPre_mem D Sc cutoff bound Λ x i h E τ Z a (hi1 ▸ ha)
    have hy := hi1 ▸ rawPost_mem D Sc cutoff bound Λ x i h E τ Z
    have hd : elvRawMixedPreDot D Sc cutoff bound Λ x i h E τ Z a ^ 2 -
        elvRawMixedPostDot D Sc cutoff bound Λ x i h E τ Z ^ 2 ∈ parity (R := k) _ _ 0 := by
      simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
        Submodule.sub_mem _ (comp_mem hx hx) (comp_mem hy hy)
    have hh := rawUnitInverse_mem _ (elvRawMixed_square_difference_isUnit
      D Sc cutoff bound Λ x i h E τ Z sy hc hi1 a (hi1 ▸ ha) hu) hd
    rw [elvRawMixedCoefficient, dite_eq_right hi]
    simpa only [End.mul_def, zero_add, hi1] using comp_mem hh (Submodule.sub_mem _ hx hy)

end OddMath.QuiverHecke.ELVOld

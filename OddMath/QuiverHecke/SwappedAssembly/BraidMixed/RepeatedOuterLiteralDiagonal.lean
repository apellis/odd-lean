/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterSeparatedCoordinates

/-! # Separated repeated-outer diagonal routes

The finite right braid sum on `Pᵢ Pⱼ Rᵢ` is the negative separated
coefficient followed by the inner mixed Q. This identifies the matrix route
needed to apply the separated-coordinate correction calculation.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
private lemma route {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ A) (r' : V ⟶ A)
    (hf : f = 0) (hr : r = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f' ≫ l) ≫ r' := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, zero_add]

variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

lemma separatedOuter_braidRight_route (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up i, up i, up j]) s _ :=
      SPath.three true false true trivial hR trivial rfl
    braidRight G i j i ν n n Z =
      (crossEntry G ν [up i] j i [] n b Z ≫ crossEntry G ν [] i i [up j] b b Z) ≫
        crossEntry G ν [up i] i j [] b n Z := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hR (SPath.two true false trivial hR rfl)
    (SPath.two true true trivial trivial rfl) Z
  have hr := crossEntry_right_eq_zero G ν i i j false true Bool.false_ne_true
    hR trivial (SPath.two true true trivial trivial rfl)
    (SPath.two true false trivial hR rfl) Z
  unfold braidRight
  erw [adjacentMixed_iij_sum hij hR rfl rfl]
  erw [adjacentMixed_iij_sum hij hR rfl rfl, adjacentMixed_iij_sum hij hR rfl rfl]
  exact route _ _ _ _ _ _ _ _ hf hr

private lemma comparison_conj {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (K : A ≅ B) (H : B ≅ V) (a : End V) (q : End A) :
    (K.hom ≫ (-(H.hom ≫ a ≫ H.inv))) ≫ (K.inv ≫ q) =
      -((K.hom ≫ H.hom ≫ a ≫ H.inv ≫ K.inv) ≫ q) := by
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]

/-- The complete finite right diagonal sum, with its coefficient and Q
identified from the supplied swapped generators. -/
lemma separatedOuter_braidRight (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫
        (P.step (true, i) true s trivial).map
          (P.mixedQ j i (nextSector (true, i) true s) hR Z)) := by
  rw [P.separatedOuter_braidRight_route ν i j s hR Z (P.swappedGens c L) hij]
  have hmid := eq_of_heq (P.adjacentReverse_target_conj_heq ν i j s c L hR Z)
  have hfirst := P.adjacentReverse_inner ν i j s c L hR Z hij
  have hlast := (P.repeatedOuter_forward_inner i j s hR Z ν c L hij).trans
    ((P.step (true, i) true s trivial).map_comp _ _)
  exact (congrArg₂ (fun f g => f ≫ g)
    (congrArg₂ (fun f g => f ≫ g) hfirst hmid) hlast).trans
    (comparison_conj (P.distinctProbeFirstIso i j i s hR Z)
      (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)) _ _)
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

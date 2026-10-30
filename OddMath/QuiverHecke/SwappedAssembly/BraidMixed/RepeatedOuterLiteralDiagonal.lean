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
section Left
variable
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))

lemma separatedOuter_braidLeft_route (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    braidLeft G i j i ν n n Z =
      (crossEntry G ν [] i j [up i] n b Z ≫ crossEntry G ν [up j] i i [] b b Z) ≫
        crossEntry G ν [] j i [up i] b n Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν i j i true true true false false true
    (by decide) trivial trivial trivial hR hR trivial rfl hs Z
  have hr := P.crossEntry_left_three_zero G ν j i i true false true true true false
    (by decide) trivial hR trivial trivial trivial hR hs rfl Z
  unfold braidLeft
  erw [adjacentMixed_jii_sum hij hR hs hs]
  erw [adjacentMixed_jii_sum hij hR hs hs, adjacentMixed_jii_sum hij hR hs hs]
  exact route _ _ _ _ _ _ _ _ hf hr

private lemma map_neg_triple {C C' : Type u} [Category C] [Preadditive C]
    [Category C'] [Preadditive C'] (F : C ⥤ C') [F.Additive]
    {A B V W : C} (f : A ⟶ B) (g : B ⟶ V) (h : V ⟶ W) :
    F.map (-(f ≫ g ≫ h)) = -(F.map f ≫ F.map g ≫ F.map h) := by
  simp only [Functor.map_neg, Functor.map_comp]

private lemma neg_assoc {C : Type u} [Category C] [Preadditive C]
    {A B V W : C} (f : A ⟶ B) (g : B ⟶ V) (h : V ⟶ W) :
    f ≫ g ≫ (-h) = -((f ≫ g) ≫ h) := by
  simp only [Preadditive.comp_neg, Category.assoc]

private lemma neg_slide {C : Type u} [Category C] [Preadditive C]
    {A B : C} (a : End A) (b : End B) (f : A ⟶ B)
    (h : a ≫ f = f ≫ b) : (-a) ≫ f = f ≫ (-b) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

include hs₀ in
lemma separatedOuter_literal_coeff_slide (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    crossEntry (P.swappedGens c L) ν [up j] i i [] b b Z ≫
        crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z =
      crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z ≫
        (-P.repeatedOuterMixedSeparatedCoeff i j s hR Z c) := by
  dsimp only
  have hB := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  have hf := P.adjacentReverse_probe_heq ν i j s c L hR hs₀ hs Z hij
  have ha := P.adjacentReverse_source_conj_heq ν i j s c L hR hs Z
  have ha' : HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR hs) Z)
      (-P.repeatedOuterMixedAdjacentCoeff i j s hR hs Z c) := by
    refine ha.trans (heq_of_eq ?_)
    have : (P.step (true, j) true s trivial).Additive := P.step_additive _ _ _ _
    exact map_neg_triple (P.step (true, j) true s trivial) _ _ _
  have hleft := comp_common_grid_heq hB hB rfl ha' hf
  have hright := comp_common_grid_heq hB rfl rfl hf
    (HEq.rfl : HEq (-P.repeatedOuterMixedSeparatedCoeff i j s hR Z c)
      (-P.repeatedOuterMixedSeparatedCoeff i j s hR Z c))
  exact eq_of_heq (hleft.trans ((heq_of_eq (neg_slide _ _ _
    (P.repeatedOuterMixed_probe_coeff i j s hR hs₀ hs Z c hc h hij))).trans hright.symm))

include hs₀ in
/-- The full left diagonal sum with the coefficient moved through the
literal terminal-cast probe edge. No probe crossing is cancelled. -/
lemma separatedOuter_braidLeft (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    braidLeft (P.swappedGens c L) i j i ν n n Z =
      -((crossEntry (P.swappedGens c L) ν [] i j [up i] n b Z ≫
        crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z) ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c) := by
  dsimp only
  rw [P.separatedOuter_braidLeft_route ν i j s hR Z hs (P.swappedGens c L) hij]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR hs) Z ≫ f)
      (P.separatedOuter_literal_coeff_slide ν i j s hR Z hs₀ hs c L hc h hij)).trans
        (neg_assoc _ _ _))
end Left
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

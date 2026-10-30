/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPostDiagonal

/-! Supported routes for the Ri Rj Pi diagonal in Brundan–Ellis (1.9).
The reservoir validity and endpoint hypotheses remain explicit. -/
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
namespace RepeatedOuterPre
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (Z : P.H (nextSector (true, j) false
    (nextSector (true, i) false (nextSector (true, i) true s))))

private lemma route {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ A) (r' : V ⟶ A)
    (hf : f' = 0) (hr : r' = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f ≫ g) ≫ r := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, add_zero]

lemma braidRight_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three false false true hi hj trivial rfl
    let b : SPath (wd D ν [up i, up i, up j]) s _ :=
      SPath.three false true false hi trivial hj rfl
    braidRight G i j i ν n n Z =
      (crossEntry G ν [up i] j i [] n b Z ≫ crossEntry G ν [] i i [up j] b b Z) ≫
        crossEntry G ν [up i] i j [] b n Z := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i j i false true (by decide)
    hi trivial (SPath.two false true hj trivial rfl) (SPath.two false false hi hj rfl) Z
  have hr := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hi (SPath.two false false hi hj rfl) (SPath.two false true hj trivial rfl) Z
  unfold braidRight
  erw [adjacentPost_iij_sum hij hi hj rfl rfl]
  erw [adjacentPost_iij_sum hij hi hj rfl rfl, adjacentPost_iij_sum hij hi hj rfl rfl]
  exact route _ _ _ _ _ _ _ _ hf hr

section Left
variable (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))

lemma braidLeft_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three false false true hi hj trivial rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three false false true hj0 hi0 trivial hs
    braidLeft G i j i ν n n Z =
      (crossEntry G ν [] i j [up i] n b Z ≫ crossEntry G ν [up j] i i [] b b Z) ≫
        crossEntry G ν [] j i [up i] b n Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν i j i false false false true true false
    (by decide) hi hj hj0 trivial trivial hi0 rfl hs Z
  have hr := P.crossEntry_left_three_zero G ν j i i false true false false false true
    (by decide) hj0 trivial hi hj hi0 trivial hs rfl Z
  unfold braidLeft
  erw [adjacentPost_jii_sum hij hj0 hi0 hs hs]
  erw [adjacentPost_jii_sum hij hj0 hi0 hs hs, adjacentPost_jii_sum hij hj0 hi0 hs hs]
  exact route _ _ _ _ _ _ _ _ hf hr
end Left

abbrev rest := P.distinctReservoirRest i i j s hj Z
abbrev middleObj := P.rpObj i i s hi (rest P i j s hj Z)
def rightIso := (P.step (true, i) false s hi).mapIso
  (P.mixedJ i j (nextSector (true, i) false s) hj Z)

lemma right_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false false true hi hj trivial rfl)
      (SPath.three false true false hi trivial hj rfl) Z =
      (rightIso P i j s hi hj Z).inv ≫
        (P.step (true, i) false s hi).map
          (P.mixedQ i j (nextSector (true, i) false s) hj Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i j i false hi
    (SPath.two false true hj trivial rfl) (SPath.two true false trivial hj rfl) Z).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  exact Functor.map_comp _ _ _

lemma right_last (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three false true false hi trivial hj rfl)
      (SPath.three false false true hi hj trivial rfl) Z =
      (rightIso P i j s hi hj Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν i i j false hi
    (SPath.two true false trivial hj rfl) (SPath.two false true hj trivial rfl) Z).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  rfl

lemma right_mid (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true false hi trivial hj rfl)
      (SPath.three false true false hi trivial hj rfl) Z =
      c.a i s hi (rest P i j s hj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two false true hi trivial rfl) (SPath.two false true hi trivial rfl)
    (.cons _ false _ hj (.nil _)) Z).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

/-- The complete right finite sum evaluated with the supplied coefficient. -/
lemma braidRight_coefficient (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial rfl)
      (SPath.three false false true hi hj trivial rfl) Z =
      ((rightIso P i j s hi hj Z).inv ≫
        (P.step (true, i) false s hi).map
          (P.mixedQ i j (nextSector (true, i) false s) hj Z) ≫
        c.a i s hi (rest P i j s hj Z)) ≫
      (rightIso P i j s hi hj Z).hom := by
  rw [braidRight_route P i j s hi hj Z ν _ hij,
    right_first P i j s hi hj Z ν c L hij,
    right_mid P i j s hi hj Z ν c L,
    right_last P i j s hi hj Z ν c L hij]
  simp only [Category.assoc]

end RepeatedOuterPre
end OddMath.QuiverHecke.SwappedAssembly

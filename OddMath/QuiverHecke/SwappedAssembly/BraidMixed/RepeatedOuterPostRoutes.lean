/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPostTransport
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReservoirOffDiagonal

/-! Literal two-reservoir diagonal path sums and their coefficient-weighted Q factors. -/
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

namespace RepeatedOuterPost
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (Z : P.H (nextSector (true, i) false
    (nextSector (true, j) false (nextSector (true, i) true s))))

private lemma route {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ A) (r' : V ⟶ A)
    (hf : f = 0) (hr : r = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f' ≫ l) ≫ r' := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, zero_add]

lemma braidLeft_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true false false trivial hj0 hi0 rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three false true false hj0 trivial hi0 rfl
    braidLeft G i j i ν n n Z =
      (crossEntry G ν [] i j [up i] n b Z ≫ crossEntry G ν [up j] i i [] b b Z) ≫
        crossEntry G ν [] j i [up i] b n Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν i j i true false false false false true
    Bool.false_ne_true trivial hj0 hj0 hi0 hi0 trivial rfl rfl Z
  have hr := P.crossEntry_left_three_zero G ν j i i false false true false true false
    (by decide) hj0 hi0 trivial hj0 trivial hi0 rfl rfl Z
  unfold braidLeft
  erw [adjacentPost_jii_sum hij hj0 hi0 rfl rfl]
  erw [adjacentPost_jii_sum hij hj0 hi0 rfl rfl, adjacentPost_jii_sum hij hj0 hi0 rfl rfl]
  exact route _ _ _ _ _ _ _ _ hf hr

lemma dotX (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (SPath.three true false false trivial hj0 hi0 rfl) Z =
      outerDot P i j s hj0 hi0 Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (SPath.two false false hj0 hi0 rfl) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_probe i (SKM.wt D ν [up j, up i]) s trivial trivial _)

lemma dotZ (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (SPath.three true false false trivial hj0 hi0 rfl) Z =
      innerDot P i j s hj0 hi0 Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two true false trivial hj0 rfl)
    (.cons _ false _ hi0 (.nil _)) (.cons _ false _ hi0 (.nil _))
    (.nil _) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) true s trivial).map
    ((P.step (true, j) false (nextSector (true, i) true s) hj0).map f))
    (P.dotImage_reservoir i ν (nextSector (true, j) false (nextSector (true, i) true s))
      hi0 hi0 Z))

lemma left_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three true false false trivial hj0 hi0 rfl)
      (SPath.three false true false hj0 trivial hi0 rfl) Z =
      (firstIso P i j s hj0 hi0 Z).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i j i
    (SPath.two true false trivial hj0 rfl) (SPath.two false true hj0 trivial rfl)
    (.cons _ false _ hi0 (.nil _)) Z).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  rfl

lemma left_last (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three false true false hj0 trivial hi0 rfl)
      (SPath.three true false false trivial hj0 hi0 rfl) Z =
      (firstIso P i j s hj0 hi0 Z).inv ≫
        P.mixedQ i j s hj0 (rest P i j s hi0 Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν j i i
    (SPath.two false true hj0 trivial rfl) (SPath.two true false trivial hj0 rfl)
    (.cons _ false _ hi0 (.nil _)) Z).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  rfl

lemma left_mid (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false true false hj0 trivial hi0 rfl)
      (SPath.three false true false hj0 trivial hi0 rfl) Z =
      (P.step (true, j) false s hj0).map
        (-((P.mixedJ i i (nextSector (true, j) false s) hi0 Z).hom ≫
          c.a i (nextSector (true, j) false s) hi0 Z ≫
          (P.mixedJ i i (nextSector (true, j) false s) hi0 Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i false hj0
    (SPath.two true false trivial hi0 rfl) (SPath.two true false trivial hi0 rfl) Z).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma braidLeft_coefficient (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three true false false trivial hj0 hi0 rfl)
      (SPath.three true false false trivial hj0 hi0 rfl) Z =
      -(coefficientAlg P i j s hj0 hi0 Z
          (c.a i (nextSector (true, j) false s) hi0 Z) ≫
        P.mixedQ i j s hj0 (rest P i j s hi0 Z)) := by
  rw [braidLeft_route P i j s hj0 hi0 Z ν _ hij,
    left_first P i j s hj0 hi0 Z ν c L hij,
    left_mid P i j s hj0 hi0 Z ν c L,
    left_last P i j s hj0 hi0 Z ν c L hij,
    coefficientAlg_apply]
  simp only [Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]

def literalCoeff (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (V : P.H t) (c : P.CrossCoeff Sc) :
    End ((P.pathFunctor (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true false false trivial hj0 hi0 e)).obj V) :=
  (conjAlg (k := k) (eqToIso (P.pathFunctor_three_obj
    (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false false trivial hj0 hi0 e V)).symm)
    (coefficientAlg P i j s hj0 hi0 (e ▸ V)
      (c.a i (nextSector (true, j) false s) hi0 (e ▸ V)))

lemma literalCoeff_heq (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (V : P.H t) (c : P.CrossCoeff Sc) :
    HEq (literalCoeff P i j s hj0 hi0 ν e V c)
      (coefficientAlg P i j s hj0 hi0 (e ▸ V)
        (c.a i (nextSector (true, j) false s) hi0 (e ▸ V))) := by
  subst e
  apply heq_of_eq
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

private lemma neg_grid {C : Type u} [Category C] [Preadditive C]
    {V W : C} (h : V = W) {a : End V} {b : End W} (he : HEq a b) : HEq (-a) (-b) := by
  subst h
  exact heq_of_eq (congrArg Neg.neg (eq_of_heq he))

private lemma qExpr_of_heq {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V W : C} (h : V = W) {x y : End V} {x' y' : End W}
    (hx : HEq x x') (hy : HEq y y') (r q : I) :
    HEq (qExpr Sc x y r q) (qExpr Sc x' y' r q) := by
  subst h
  rw [eq_of_heq hx, eq_of_heq hy]

section Transport
variable (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))

lemma braidRight_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true false false trivial hj0 hi0 hs
    let b : SPath (wd D ν [up i, up i, up j]) s _ :=
      SPath.three true false false trivial hi hj rfl
    braidRight G i j i ν n n Y =
      (crossEntry G ν [up i] j i [] n b Y ≫ crossEntry G ν [] i i [up j] b b Y) ≫
        crossEntry G ν [up i] i j [] b n Y := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hi (SPath.two false false hj0 hi0 hs) (SPath.two true false trivial hj rfl) Y
  have hr := crossEntry_right_eq_zero G ν i i j false true (by decide)
    hi trivial (SPath.two true false trivial hj rfl) (SPath.two false false hj0 hi0 hs) Y
  unfold braidRight
  erw [adjacentPost_iij_sum hij hi hj rfl rfl]
  erw [adjacentPost_iij_sum hij hi hj rfl rfl, adjacentPost_iij_sum hij hi hj rfl rfl]
  exact route _ _ _ _ _ _ _ _ hf hr

lemma right_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three true false false trivial hj0 hi0 hs)
      (SPath.three true false false trivial hi hj rfl) Y)
      (reservoirCross P i j s hj0 hi0 hi hj hs Y) := by
  exact P.distinctReservoir_right ν i j i s hj0 hi0 hi hj hs c L Y hij.symm

lemma right_mid (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false false trivial hi hj rfl)
      (SPath.three true false false trivial hi hj rfl) Y =
      -(targetAlg P i j s hi hj Y (c.a i s hi (P.distinctReservoirRest i i j s hj Y))) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two true false trivial hi rfl) (SPath.two true false trivial hi rfl)
    (.cons _ false _ hj (.nil _)) Y).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma right_coeff_slide (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j i []
        (SPath.three true false false trivial hj0 hi0 hs)
        (SPath.three true false false trivial hi hj rfl) Y ≫
      crossEntry (P.swappedGens c L) ν [] i i [up j]
        (SPath.three true false false trivial hi hj rfl)
        (SPath.three true false false trivial hi hj rfl) Y)
      ((-coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Y))) ≫
          reservoirCross P i j s hj0 hi0 hi hj hs Y) := by
  rw [right_mid P i j s hi hj Y ν c L]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false false trivial hj0 hi0 hs Y
  refine (comp_common_grid_heq hn rfl rfl (right_first P i j s hj0 hi0 hi hj hs Y ν c L hij)
    (HEq.rfl)).trans ?_
  apply heq_of_eq
  rw [Preadditive.comp_neg, Preadditive.neg_comp, coeff_slide P i j s hj0 hi0 hi hj hs Y c hc h hij]

lemma right_literal_slide (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true false false trivial hj0 hi0 hs
    let b : SPath (wd D ν [up i, up i, up j]) s _ :=
      SPath.three true false false trivial hi hj rfl
    crossEntry (P.swappedGens c L) ν [up i] j i [] n b Y ≫
      crossEntry (P.swappedGens c L) ν [] i i [up j] b b Y =
    (-literalCoeff P i j s hj0 hi0 ν hs Y c) ≫
      crossEntry (P.swappedGens c L) ν [up i] j i [] n b Y := by
  dsimp only
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false false trivial hj0 hi0 hs Y
  have ha : HEq (-literalCoeff P i j s hj0 hi0 ν hs Y c)
      (-coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Y))) := by
    exact neg_grid hn (literalCoeff_heq P i j s hj0 hi0 ν hs Y c)
  have hr := comp_common_grid_heq hn hn rfl ha
    (right_first P i j s hj0 hi0 hi hj hs Y ν c L hij)
  exact eq_of_heq ((right_coeff_slide P i j s hj0 hi0 hi hj hs Y ν c L hc h hij).trans hr.symm)

lemma right_quad (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j i []
        (SPath.three true false false trivial hj0 hi0 hs)
        (SPath.three true false false trivial hi hj rfl) Y ≫
      crossEntry (P.swappedGens c L) ν [up i] i j []
        (SPath.three true false false trivial hi hj rfl)
        (SPath.three true false false trivial hj0 hi0 hs) Y)
      (qExpr Sc (middleDot P i j s hj0 hi0 (hs ▸ Y))
        (innerDot P i j s hj0 hi0 (hs ▸ Y)) j i) := by
  classical
  let p : SPath (wd D ν [up j, up i]) (nextSector (true, i) true s) _ :=
    SPath.two false false hj0 hi0 hs
  let b : SPath (wd D ν [up i, up j]) (nextSector (true, i) true s) _ :=
    SPath.two false false hi hj rfl
  have hsum : crossCross (P.swappedGens c L) j i ν p p Y =
      (P.swappedGens c L).cross j i ν p b Y ≫ (P.swappedGens c L).cross i j ν b p Y := by
    have : Subsingleton (SPath (wd D ν [up i, up j]) (nextSector (true, i) true s)
        (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))) :=
      ⟨path_eq_of_ne hij⟩
    let : Fintype (SPath (wd D ν [up i, up j]) (nextSector (true, i) true s)
        (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))) :=
      Fintype.ofFinite _
    unfold crossCross
    exact Fintype.sum_subsingleton _ b
  have hq := congrArg (P.step (true, i) true s trivial).map
    (hsum.symm.trans (P.swappedGens_crossCrossNe c L j i ν hij.symm p Y))
  rw [Functor.map_comp] at hq
  have hmap := qExpr_map Sc (functorAlg (k := k) (P.step (true, i) true s trivial) _)
    (leftDot (P.swappedGens c L) j i ν p Y) (rightDot (P.swappedGens c L) j i ν p Y) j i
  erw [crossEntry_right, crossEntry_right]
  refine (heq_of_eq (hq.trans hmap)).trans ?_
  have hp := P.pathFunctor_two_obj
    (c₁ := ⟨up j, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
    (t := nextSector (true, i) true s)
    false false hj0 hi0 hs Y _ (P.sector_heq hs Y)
  exact qExpr_of_heq (Sc := Sc) (congrArg (P.step (true, i) true s trivial).obj hp)
    (map_of_heq _ hp hp (P.leftDot_two_reservoir_heq c L j i ν (s := nextSector (true, i) true s) hj0 false hi0 hs Y _
      (P.sector_heq hs Y)))
    (map_of_heq _ hp hp (P.rightDot_two_reservoir_heq c L j i ν (s := nextSector (true, i) true s) false hj0 hi0 hs Y _
      (P.sector_heq hs Y))) j i

include hi hj in
lemma braidRight_coefficient (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    HEq (braidRight (P.swappedGens c L) i j i ν
      (SPath.three true false false trivial hj0 hi0 hs)
      (SPath.three true false false trivial hj0 hi0 hs) Y)
      (-(coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Y)) ≫
        qExpr Sc (middleDot P i j s hj0 hi0 (hs ▸ Y))
          (innerDot P i j s hj0 hi0 (hs ▸ Y)) j i)) := by
  rw [braidRight_route P i j s hj0 hi0 hi hj hs Y ν _ hij,
    right_literal_slide P i j s hj0 hi0 hi hj hs Y ν c L hc h hij, Category.assoc]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false false trivial hj0 hi0 hs Y
  have ha := neg_grid hn (literalCoeff_heq P i j s hj0 hi0 ν hs Y c)
  refine (comp_common_grid_heq hn hn hn ha
    (right_quad P i j s hj0 hi0 hi hj hs Y ν c L hij)).trans ?_
  exact heq_of_eq (Preadditive.neg_comp _ _)

end Transport


end RepeatedOuterPost
end OddMath.QuiverHecke.SwappedAssembly

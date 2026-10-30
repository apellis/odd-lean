/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReduction

/-! # Remaining repeated-outer mixed entries

The coefficient-free off-diagonal route from `Pᵢ Pⱼ Rᵢ` to `Rᵢ Pⱼ Pᵢ`
uses the actual mixed comparisons, including the equal-colour matrix entry.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u,u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

section Move
variable (ν : X) (i j r : I) (s : Sector I) (hR : StepValid (true, r) false s)
  {t : Sector I}
  (e : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData) (Z : P.H t)
/-- The two comparison entries do not require distinct reservoir and probe colours. -/
theorem mixedProbe_move_heq :
    HEq
      (crossEntry (P.swappedGens c L) ν [up i] j r []
          (distinctProbeSource ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z ≫
        crossEntry (P.swappedGens c L) ν [] i r [up j]
          (distinctProbeMiddle ν i j r s hR e) (distinctProbeTarget ν i j r s hR e) Z)
      ((P.step (true, i) true s trivial).map
          (P.mixedJ j r (nextSector (true, i) true s) hR (e ▸ Z)).hom ≫
        (P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).hom) := by
  subst e
  apply heq_of_eq
  apply congrArg₂ (· ≫ ·)
  · refine (crossEntry_right (P.swappedGens c L) ν i j r true trivial
      (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
      (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z).trans ?_
    by_cases hjr : j = r
    · subst j
      erw [swappedGens_cross_self]
      rfl
    · dsimp only [swappedGens]
      erw [P.crossImage_ne c hjr]
      rfl
  · refine (crossEntry_left (P.swappedGens c L) ν i r j
      (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
      (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
      (.cons _ true _ trivial (.nil _)) Z).trans ?_
    apply eq_of_heq
    refine (sandwich_heq _ _ _).trans ?_
    by_cases hir : i = r
    · subst i
      erw [swappedGens_cross_self]
      rfl
    · dsimp only [swappedGens]
      erw [P.crossImage_ne c hir]
      rfl
end Move

section OuterEdges
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, j) true (nextSector (true, i) true s) =
    nextSector (true, i) true (nextSector (true, j) true s))
  (hsR : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)))
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s))))

/-- The left probe crossing, including its source-object transport. -/
theorem repeatedOuter_other_left (hij : i ≠ j) :
    (P.pathFunctor (distinctProbeSource (D := D) ν i j i s hR hsR)).obj Z =
        (P.step (true, i) true s trivial).obj
          ((P.step (true, j) true (nextSector (true, i) true s) trivial).obj
            (hs ▸ (P.step (true, i) false
              (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z)) ∧
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (distinctProbeSource ν i j i s hR hsR) (distinctProbeSource ν j i i s hR rfl) Z)
      (P.preCrossNe i j s hs ((P.step (true, i) false
        (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z)) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial hs
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, i) true (nextSector (true, j) true s))
      (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s))) :=
    .cons _ false _ hR (.nil _)
  have hp : distinctProbeSource (D := D) ν i j i s hR hsR = pg.append pv :=
    by
      rcases adjacentMixed_iji_cases hij hR rfl hsR (pg.append pv) with h | h
      · cases h
      · exact h.symm
  have hq : distinctProbeSource (D := D) ν j i i s hR rfl = qg.append pv := rfl
  rw [hp, hq]
  constructor
  · erw [P.pathFunctor_append]
    exact P.pathFunctor_two_obj
      (c₁ := ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up j]⟩)
      (c₂ := ⟨up j, SKM.wt D (SKM.wt D ν [up i]) []⟩)
      true true trivial trivial hs _ _ (P.sector_heq hs _)
  · erw [crossEntry_left]
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hij]
    exact P.twoTwo_two_heq
      ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up j]⟩ ⟨up j, SKM.wt D ν [up i]⟩
      ⟨up j, SKM.wt D (SKM.wt D ν [up i]) [up i]⟩ ⟨up i, SKM.wt D ν [up i]⟩
      (P.crossNeEntry i j _ _ _ _) (t := s) true true true true
      trivial trivial trivial trivial hs rfl rfl _ _ HEq.rfl
end OuterEdges

private lemma other_route {C : Type u} [Category C] [Preadditive C]
    {A B V T : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ T) (r' : V ⟶ T)
    (hf : f = 0) (hr : r' = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f' ≫ h) ≫ r := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, zero_add, add_zero]

section Routes
variable (G : P.Generators) (ν : X) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hsR : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)))
  (Z : P.H (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s))))

/-- Spectator vanishing leaves the coefficient-free left off-diagonal route. -/
theorem repeatedOuter_other_left_route (hij : i ≠ j) :
    let n := distinctProbeSource (D := D) ν i j i s hR hsR
    let m := distinctProbeTarget (D := D) ν j i i s hR rfl
    let a := distinctProbeMiddle (D := D) ν j i i s hR rfl
    let b := distinctProbeSource (D := D) ν j i i s hR rfl
    braidLeft G i j i ν n m Z =
      (crossEntry G ν [] i j [up i] n b Z ≫ crossEntry G ν [up j] i i [] b a Z) ≫
        crossEntry G ν [] j i [up i] a m Z := by
  classical
  let n := distinctProbeSource (D := D) ν i j i s hR hsR
  let m := distinctProbeTarget (D := D) ν j i i s hR rfl
  let a := distinctProbeMiddle (D := D) ν j i i s hR rfl
  let b := distinctProbeSource (D := D) ν j i i s hR rfl
  change braidLeft G i j i ν n m Z =
    (crossEntry G ν [] i j [up i] n b Z ≫ crossEntry G ν [up j] i i [] b a Z) ≫
      crossEntry G ν [] j i [up i] a m Z
  have hf := P.crossEntry_left_three_zero G ν i j i true true true false false true
    Bool.false_ne_true trivial trivial trivial hR hR trivial hsR rfl Z
  have hr := P.crossEntry_left_three_zero G ν j i i true true false true false true
    Bool.false_ne_true trivial trivial hR trivial hR trivial rfl rfl Z
  unfold braidLeft
  erw [adjacentMixed_jii_sum (ν := ν) hij hR rfl rfl]
  erw [adjacentMixed_jii_sum (ν := ν) hij hR rfl rfl,
    adjacentMixed_jii_sum (ν := ν) hij hR rfl rfl]
  exact other_route _ _ _ _ _ _ _ _ hf hr

/-- Spectator vanishing leaves the coefficient-free right off-diagonal route. -/
theorem repeatedOuter_other_right_route (hij : i ≠ j) :
    let n := distinctProbeSource (D := D) ν i j i s hR hsR
    let m := distinctProbeTarget (D := D) ν j i i s hR rfl
    let a := distinctProbeTarget (D := D) ν i j i s hR hsR
    let b := distinctProbeMiddle (D := D) ν i j i s hR hsR
    braidRight G i j i ν n m Z =
      (crossEntry G ν [up i] j i [] n b Z ≫ crossEntry G ν [] i i [up j] b a Z) ≫
        crossEntry G ν [up i] i j [] a m Z := by
  classical
  let n := distinctProbeSource (D := D) ν i j i s hR hsR
  let m := distinctProbeTarget (D := D) ν j i i s hR rfl
  let a := distinctProbeTarget (D := D) ν i j i s hR hsR
  let b := distinctProbeMiddle (D := D) ν i j i s hR hsR
  change braidRight G i j i ν n m Z =
    (crossEntry G ν [up i] j i [] n b Z ≫ crossEntry G ν [] i i [up j] b a Z) ≫
      crossEntry G ν [up i] i j [] a m Z
  have hf := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hR (SPath.two true false trivial hR hsR)
    (SPath.two true true trivial trivial hsR) Z
  have hr := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hR (SPath.two false true hR trivial hsR)
    (SPath.two true true trivial trivial rfl) Z
  unfold braidRight
  rw [adjacentMixed_iij_sum hij hR hsR hsR]
  simp only [adjacentMixed_iij_sum hij hR hsR hsR]
  exact other_route _ _ _ _ _ _ _ _ hf hr
end Routes

/-- The actual repeated-outer off-diagonal entry from `PᵢPⱼRᵢ` to `RᵢPⱼPᵢ`.
Neither inverse-denominator data nor any assumed matrix braid is required. -/
theorem repeatedOuter_other_offDiag (ν : X) (i j : I) (s : Sector I)
    (hR : StepValid (true, i) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j)
    (hsR : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    braidLeft (P.swappedGens c L) i j i ν
      (distinctProbeSource ν i j i s hR hsR) (distinctProbeTarget ν j i i s hR rfl) Z =
    braidRight (P.swappedGens c L) i j i ν
      (distinctProbeSource ν i j i s hR hsR) (distinctProbeTarget ν j i i s hR rfl) Z := by
  classical
  have hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s) := by
    simp only [nextSector, add_right_comm]
  rw [P.repeatedOuter_other_left_route (P.swappedGens c L) ν i j s hR hsR Z hij,
    P.repeatedOuter_other_right_route (P.swappedGens c L) ν i j s hR hsR Z hij]
  obtain ⟨hA, hf⟩ := P.repeatedOuter_other_left ν i j s hR hs hsR c L Z hij
  have h := rectangle_of_heq hA (P.distinctProbeSource_obj ν i j i s hR hsR Z) rfl
    (P.distinctProbeTarget_obj ν i j i s hR hsR Z) rfl hf
    (P.mixedProbe_move_heq ν j i i s hR rfl c L Z)
    (P.mixedProbe_move_heq ν i j i s hR hsR c L Z)
    (P.distinctProbe_right ν i j i s hR hsR c L Z hij)
    ((P.preCrossNe_mixedJ_pair_heq i j i s hR hs hsR Z).trans
      (heq_of_eq (Category.assoc _ _ _).symm))
  exact (Category.assoc _ _ _).trans h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

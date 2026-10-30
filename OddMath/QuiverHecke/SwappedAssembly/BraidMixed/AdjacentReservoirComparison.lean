/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReservoirOffDiagonal

/-! # Adjacent-equal two-reservoir comparison braid

The coefficient-free mixed-comparison entry Pi Ri Rj to Rj Ri Pi
of Brundan–Ellis (1.9). The other entries of this block remain separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

section ReservoirEdges
variable (ν : X) (i q : I) (s : Sector I)
  (hr : StepValid (true, i) false s)
  (hq : StepValid (true, q) false (nextSector (true, i) false s))
  (hq' : StepValid (true, q) false s)
  (hr' : StepValid (true, i) false (nextSector (true, q) false s))
  (hs : nextSector (true, q) false (nextSector (true, i) false s) =
    nextSector (true, i) false (nextSector (true, q) false s))
  (hsP : nextSector (true, q) false (nextSector (true, i) false (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, q) false (nextSector (true, i) true s)))
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, i) false (nextSector (true, q) false (nextSector (true, i) true s))))

/-- The reservoir crossing with the probe on the right, including its endpoint comparison. -/
theorem adjacentReservoir_left (hiq : i ≠ q) :
    HEq (crossEntry (P.swappedGens c L) ν [] i q [up i]
      (distinctReservoirTarget ν i i q s hr hq hsP)
      (distinctReservoirTarget ν i q i s hq' hr' rfl) Z)
      ((P.step (true, i) false s hr).map
        ((P.step (true, q) false (nextSector (true, i) false s) hq).map
          (eqToHom (P.probe_obj_sector_transport i hs Z))) ≫
        P.postCrossNe i q s hr hq hq' hr' hs
          ((P.step (true, i) true (nextSector (true, i) false
            (nextSector (true, q) false s)) trivial).obj Z)) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up i, up q]) s
      (nextSector (true, i) false (nextSector (true, q) false s)) :=
    SPath.two false false hr hq hs
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up q, up i]) s
      (nextSector (true, i) false (nextSector (true, q) false s)) :=
    SPath.two false false hq' hr' rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, i) false (nextSector (true, q) false s))
      (nextSector (true, i) false (nextSector (true, q) false (nextSector (true, i) true s))) :=
    .cons _ true _ trivial (.nil _)
  have hp : distinctReservoirTarget (D := D) ν i i q s hr hq hsP = pg.append pv :=
by
      rcases adjacentPost_iji_cases hiq hr hq hq' hr' hsP rfl (pg.append pv) with h | h
      · exact h.symm
      · cases h
  have hqg : distinctReservoirTarget (D := D) ν i q i s hq' hr' rfl = qg.append pv := rfl
  rw [hp, hqg]
  erw [crossEntry_left]
  have hed : HEq
      (crossEntry (P.swappedGens c L) ν [] i q [up i] (pg.append pv) (qg.append pv) Z)
      (P.postCrossNe i q s hr hq hq' hr' hs
        ((P.step (true, i) true _ trivial).obj Z)) := by
    erw [crossEntry_left]
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hiq]
    exact P.twoTwo_two_heq
      ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up q]⟩ ⟨up q, SKM.wt D ν [up i]⟩
      ⟨up q, SKM.wt D (SKM.wt D ν [up i]) [up i]⟩ ⟨up i, SKM.wt D ν [up i]⟩
      (P.crossNeEntry i q _ _ _ _) (t := s) false false false false
      hr hq hq' hr' hs rfl rfl _ _ HEq.rfl
  erw [crossEntry_left] at hed
  refine hed.trans ?_
  symm
  rw [eqToHom_map, eqToHom_map]
  simpa only [eqToHom_refl, Category.comp_id] using sandwich_heq
    (congrArg (fun Y => (P.step (true, i) false s hr).obj
      ((P.step (true, q) false (nextSector (true, i) false s) hq).obj Y))
      (P.probe_obj_sector_transport i hs Z)) rfl
    (P.postCrossNe i q s hr hq hq' hr' hs
      ((P.step (true, i) true _ trivial).obj Z))
end ReservoirEdges



private lemma adjacent_left_sum {C : Type u} [Category C] [Preadditive C]
    {A B V U W T : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ U)
    (h : V ⟶ U) (j : B ⟶ W) (l : V ⟶ W) (r : U ⟶ T) (r' : W ⟶ T)
    (hh : h = 0) (hr : r' = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f ≫ g) ≫ r := by
  rw [hh, hr]
  simp only [Limits.comp_zero, add_zero]

private lemma adjacent_right_sum {C : Type u} [Category C] [Preadditive C]
    {A B V U W T : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ U)
    (h : V ⟶ U) (j : B ⟶ W) (l : V ⟶ W) (r : U ⟶ T) (r' : W ⟶ T)
    (hf : f = 0) (hh : h = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f' ≫ l) ≫ r' := by
  rw [hf, hh]
  simp only [Limits.comp_zero, Limits.zero_comp, zero_add]

section Routes
variable (ν : X) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj₀ : StepValid (true, j) false s)
  (hi₀ : StepValid (true, i) false (nextSector (true, j) false s))
  (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)))
  (Z : P.H (nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s))))

lemma adjacentReservoir_left_route (G : P.Generators) (hij : i ≠ j) :
    let n := distinctReservoirSource (D := D) ν i i j s hi hj e
    let m := distinctReservoirTarget (D := D) ν i j i s hj₀ hi₀ rfl
    let a := distinctReservoirMiddle (D := D) ν i i j s hi hj e
    let b := distinctReservoirTarget (D := D) ν i i j s hi hj e
    braidLeft G i i j ν n m Z =
      (crossEntry G ν [] i i [up j] n a Z ≫ crossEntry G ν [up i] i j [] a b Z) ≫
        crossEntry G ν [] i j [up i] b m Z := by
  classical
  dsimp only
  have hh := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hi (SPath.two false false hi hj e)
    (SPath.two false true hj trivial e) Z
  have hr := P.crossEntry_left_three_zero G ν i j i true false false false false true
    Bool.false_ne_true trivial hj₀ hj₀ hi₀ hi₀ trivial rfl rfl Z
  unfold braidLeft
  erw [adjacentPost_iji_sum (ν := ν) hij hi hj hj₀ hi₀ e rfl]
  erw [adjacentPost_iij_sum (ν := ν) hij hi hj e e,
    adjacentPost_iij_sum (ν := ν) hij hi hj e e]
  exact adjacent_left_sum _ _ _ _ _ _ _ _ hh hr

lemma adjacentReservoir_right_route (G : P.Generators) (hij : i ≠ j) :
    let n := distinctReservoirSource (D := D) ν i i j s hi hj e
    let m := distinctReservoirTarget (D := D) ν i j i s hj₀ hi₀ rfl
    let a := distinctReservoirSource (D := D) ν i j i s hj₀ hi₀ rfl
    let b := distinctReservoirMiddle (D := D) ν i j i s hj₀ hi₀ rfl
    braidRight G i i j ν n m Z =
      (crossEntry G ν [up i] i j [] n a Z ≫ crossEntry G ν [] i j [up i] a b Z) ≫
        crossEntry G ν [up j] i i [] b m Z := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hi (SPath.two false false hi hj e)
    (SPath.two false true hj trivial e) Z
  have hh := P.crossEntry_left_three_zero G ν i j i true false false false false true
    Bool.false_ne_true trivial hj₀ hj₀ hi₀ hi₀ trivial rfl rfl Z
  unfold braidRight
  erw [adjacentPost_jii_sum (ν := ν) hij hj₀ hi₀ rfl rfl]
  erw [adjacentPost_iji_sum (ν := ν) hij hi hj hj₀ hi₀ e rfl,
    adjacentPost_iji_sum (ν := ν) hij hi hj hj₀ hi₀ e rfl]
  exact adjacent_right_sum _ _ _ _ _ _ _ _ hf hh

/-- The literal coefficient-free comparison entry in the adjacent-equal
mixed block with a reservoir spectator. -/
theorem adjacentReservoir_comparison_braid (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (distinctReservoirSource ν i i j s hi hj e)
      (distinctReservoirTarget ν i j i s hj₀ hi₀ rfl) Z =
    braidRight (P.swappedGens c L) i i j ν
      (distinctReservoirSource ν i i j s hi hj e)
      (distinctReservoirTarget ν i j i s hj₀ hi₀ rfl) Z := by
  have hs : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    simp only [nextSector, tsub_right_comm]
  rw [P.adjacentReservoir_left_route ν i j s hi hj hj₀ hi₀ e Z _ hij,
    P.adjacentReservoir_right_route ν i j s hi hj hj₀ hi₀ e Z _ hij]
  symm
  erw [Category.assoc]
  exact rectangle_of_heq
    (P.distinctReservoirSource_obj ν i i j s hi hj e Z)
    (P.distinctReservoirSource_obj ν i i j s hi hj e Z)
    rfl (P.distinctReservoirTarget_obj ν i i j s hi hj e Z) rfl
    (P.distinctReservoir_right ν i i j s hi hj hj₀ hi₀ e c L Z hij)
    (P.mixedReservoir_move_heq ν i j i s hj₀ hi₀ rfl c L Z)
    (P.mixedReservoir_move_heq ν i i j s hi hj e c L Z)
    (P.adjacentReservoir_left ν i j s hi hj hj₀ hi₀ hs e c L Z hij)
    (by
      apply heq_of_eq
      refine (eq_of_heq (P.postCrossNe_mixedJ_pair_heq i i j s hi hj hj₀ hi₀ hs e Z)).trans ?_
      exact (Category.assoc _ _ _).symm)
end Routes

/-- Adjacent-equal two-reservoir comparison entry at arbitrary terminal sectors. -/
theorem adjacentReservoir_comparison_braid_transport (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hj₀ : StepValid (true, j) false s)
    (hi₀ : StepValid (true, i) false (nextSector (true, j) false s))
    {t : Sector I}
    (e₀ : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e₁ : nextSector (true, i) true (nextSector (true, i) false (nextSector (true, j) false s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three true false false trivial hi hj e₀)
      (SPath.three false false true hj₀ hi₀ trivial e₁) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three true false false trivial hi hj e₀)
      (SPath.three false false true hj₀ hi₀ trivial e₁) Z := by
  subst e₁
  exact P.adjacentReservoir_comparison_braid ν i j s hi hj hj₀ hi₀ e₀ Z c L hij
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

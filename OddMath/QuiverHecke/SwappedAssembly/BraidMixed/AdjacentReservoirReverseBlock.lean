/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirReverseComparison

/-! The complete opposite adjacent-equal two-reservoir braid block. -/
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
namespace AdjacentReservoirReverseBlock
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (Z : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))

private lemma route_right {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hf : f₁ = 0) (hg : g₀₁ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₀ ≫ g₀₀) ≫ r₀ := by
  rw [hf, hg]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero]


private lemma square_route {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hr : r₀ = 0) (hg : g₀₁ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₁ ≫ g₁₁) ≫ r₁ := by
  rw [hr, hg]
  simp only [Limits.comp_zero, zero_add]

private lemma route_reverse {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hf : f₀ = 0) (hg : g₁₀ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₁ ≫ g₁₁) ≫ r₁ := by
  rw [hf, hg]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero, zero_add]


private lemma remaining {C : Type u} [Category C] [Preadditive C]
    {M A V U : C} (E : A ≅ M) (K : U ≅ V) (X : V ⟶ M) (Y : U ⟶ A)
    (a : M ⟶ M) (b : V ⟶ V)
    (hc : X ≫ a = b ≫ X) (hr : Y ≫ E.hom = K.hom ≫ X) :
    (X ≫ (-(a ≫ a ≫ E.inv)) = (-(b ≫ b ≫ K.inv)) ≫ Y) ∧
    (Y ≫ (-(E.hom ≫ a ≫ E.inv)) = (-(K.hom ≫ b ≫ K.inv)) ≫ Y) := by
  have hy : Y = K.hom ≫ X ≫ E.inv := by
    have he := congrArg (fun g => g ≫ E.inv) hr
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  constructor
  · rw [hy]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc X a, hc]
    simp only [Category.assoc]
    rw [← Category.assoc X a, hc]
    simp only [Category.assoc]
  · rw [hy]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc X a, hc]
    simp only [Category.assoc]

lemma left_square_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial hs
    let a : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    let b : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj rfl
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three true false false trivial hi hj rfl
    braidLeft G j i i ν n m Z =
      (crossEntry G ν [] j i [up i] n a Z ≫ crossEntry G ν [up i] j i [] a b Z) ≫
        crossEntry G ν [] i i [up j] b m Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν j i i false false true false true false
    (by decide) hj0 hi0 trivial hj0 trivial hi0 hs hs Z
  have hg := crossEntry_right_eq_zero G ν i j i false true (by decide)
    hi trivial (SPath.two false true hj trivial rfl) (SPath.two false false hi hj rfl) Z
  unfold braidLeft
  erw [adjacentPost_iij_sum hij hi hj rfl rfl]
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 rfl hs, adjacentPost_iji_sum hij hi hj hj0 hi0 rfl hs]
  exact route_right _ _ _ _ _ _ _ _ hf hg

lemma left_diag_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 hs
    let a : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three true false false trivial hj0 hi0 hs
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three true false false trivial hi hj rfl
    braidLeft G j i i ν n m Z =
      (crossEntry G ν [] j i [up i] n a Z ≫ crossEntry G ν [up i] j i [] a m Z) ≫
        crossEntry G ν [] i i [up j] m m Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν j i i false true false false false true
    (by decide) hj0 trivial hi hj hi0 trivial hs rfl Z
  have hg := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hi (SPath.two false false hj0 hi0 hs) (SPath.two true false trivial hj rfl) Z
  unfold braidLeft
  erw [adjacentPost_iij_sum hij hi hj rfl rfl]
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 rfl hs, adjacentPost_iji_sum hij hi hj hj0 hi0 rfl hs]
  exact route_reverse _ _ _ _ _ _ _ _ hf hg

lemma right_route (ν : X) (G : P.Generators) (hij : i ≠ j)
    (n : SPath (wd D ν [up j, up i, up i]) s _) :
    let a : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three true false false trivial hj0 hi0 hs
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three true false false trivial hi hj rfl
    braidRight G j i i ν n m Z =
      (crossEntry G ν [up j] i i [] n a Z ≫ crossEntry G ν [] j i [up i] a b Z) ≫
        crossEntry G ν [up i] j i [] b m Z := by
  classical
  dsimp only
  have hg := P.crossEntry_left_three_zero G ν j i i false false true false true false
    (by decide) hj0 hi0 trivial hj0 trivial hi0 hs hs Z
  have hr := crossEntry_right_eq_zero G ν i j i false true (by decide)
    hi trivial (SPath.two false true hj trivial rfl) (SPath.two false false hi hj rfl) Z
  unfold braidRight
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 rfl hs]
  erw [adjacentPost_jii_sum hij hj0 hi0 hs hs, adjacentPost_jii_sum hij hj0 hi0 hs hs]
  exact square_route _ _ _ _ _ _ _ _ hr hg

lemma source_square (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false false true hj0 hi0 trivial hs)
      (SPath.three false true false hj0 trivial hi0 hs) Z)
      ((P.step (true, j) false s hj0).map
        (-(c.a i (nextSector (true, j) false s) hi0 (hs ▸ Z) ≫
          c.a i (nextSector (true, j) false s) hi0 (hs ▸ Z) ≫
          (P.mixedJ i i (nextSector (true, j) false s) hi0 (hs ▸ Z)).inv))) := by
  generalize ht : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t at Z hs
  subst hs
  exact heq_of_eq (RepeatedOuterReservoirReverse.left_middle P i j s hj0 hi0 Z ν c L)

lemma source_diag (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three false true false hj0 trivial hi0 hs) Z)
      ((P.step (true, j) false s hj0).map
        (-((P.mixedJ i i (nextSector (true, j) false s) hi0 (hs ▸ Z)).hom ≫
          c.a i (nextSector (true, j) false s) hi0 (hs ▸ Z) ≫
          (P.mixedJ i i (nextSector (true, j) false s) hi0 (hs ▸ Z)).inv))) := by
  generalize ht : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t at Z hs
  subst hs
  apply heq_of_eq
  refine (crossEntry_right (P.swappedGens c L) ν j i i false hj0
    (SPath.two true false trivial hi0 rfl) (SPath.two true false trivial hi0 rfl) Z).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma target_diag (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false false trivial hi hj rfl)
      (SPath.three true false false trivial hi hj rfl) Z =
      (-((P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj Z)).hom ≫
        c.a i s hi (RepeatedOuterPre.rest P i j s hj Z) ≫
        (P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj Z)).inv)) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two true false trivial hi rfl) (SPath.two true false trivial hi rfl)
    (.cons _ false _ hj (.nil _)) Z).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma target_square (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true false hi trivial hj rfl)
      (SPath.three true false false trivial hi hj rfl) Z =
      (-(c.a i s hi (RepeatedOuterPre.rest P i j s hj Z) ≫
        c.a i s hi (RepeatedOuterPre.rest P i j s hj Z) ≫
        (P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj Z)).inv)) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two false true hi trivial rfl) (SPath.two true false trivial hi rfl)
    (.cons _ false _ hj (.nil _)) Z).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma native_pair
    (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let E := P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj Z)
    let K := (P.step (true, j) false s hj0).mapIso
      (P.mixedJ i i (nextSector (true, j) false s) hi0 (hs ▸ Z))
    let a := c.a i s hi (RepeatedOuterPre.rest P i j s hj Z)
    let b := (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Z))
    let X := RepeatedOuterPre.reservoirBack P i j s hi hj hj0 hi0 hs0 Z ≫
      (RepeatedOuterPre.rightIso P i j s hi hj Z).inv ≫
      (P.step (true, i) false s hi).map (P.mixedQ i j (nextSector (true, i) false s) hj Z)
    let Y := ((RepeatedOuterPost.firstIso P i j s hj0 hi0 (hs ▸ Z)).inv ≫
      P.mixedQ i j s hj0 (P.distinctReservoirRest i j i s hi0 (hs ▸ Z))) ≫
      RepeatedOuterPost.reservoirCross P i j s hj0 hi0 hi hj hs Z
    (X ≫ (-(a ≫ a ≫ E.inv)) = (-(b ≫ b ≫ K.inv)) ≫ Y) ∧
    (Y ≫ (-(E.hom ≫ a ≫ E.inv)) = (-(K.hom ≫ b ≫ K.inv)) ≫ Y) := by
  dsimp only
  apply remaining
  · exact (AdjacentReservoirReverseCoefficient.native_entry P i j s hi hj hj0 hi0 hs Z hs0 c hc h hij).trans
      (Category.assoc _ _ _)
  · exact (AdjacentReservoirReverseComparison.native_entry P i j s hi hj hj0 hi0 hs Z hs0 hij).trans
      (Category.assoc _ _ _)

lemma square_braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial hs)
      (SPath.three true false false trivial hi hj rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial hs)
      (SPath.three true false false trivial hi hj rfl) Z := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs.symm
    exact Prod.ext rfl he2
  erw [left_square_route P i j s hi hj hj0 hi0 hs Z ν _ hij,
    right_route P i j s hi hj hj0 hi0 hs Z ν _ hij]
  have hn := P.distinctReservoirTarget_obj ν i j i s hj0 hi0 hs Z
  have hu := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false true false hj0 trivial hi0 hs Z
  have ht := P.distinctReservoirSource_obj ν i j i s hj0 hi0 hs Z
  have hl₁ := P.repeatedReservoir_left ν i j s hj0 hi0 hi hj hs0.symm hs c L Z hij
  have hl₂ := heq_of_eq (RepeatedOuterPre.right_first P i j s hi hj Z ν c L hij)
  have hl₃ := heq_of_eq (target_square P i j s hi hj Z ν c L)
  have hr₁ := source_square P i j s hj0 hi0 hs Z ν c L
  simp only [Functor.map_neg, Functor.map_comp] at hr₁
  have hr₂ := AdjacentReservoirReverseComparison.left_first P i j s hj0 hi0 hs Z ν c L hij
  have hr₃ := P.distinctReservoir_right ν i j i s hj0 hi0 hi hj hs c L Z hij.symm
  have hl := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn rfl rfl hl₁ hl₂) hl₃
  have hr := comp_common_grid_heq hn hu rfl hr₁ (comp_common_grid_heq hu ht rfl hr₂ hr₃)
  have hr' := (heq_of_eq (Category.assoc _ _ _)).trans hr
  exact eq_of_heq (hl.trans ((heq_of_eq
    (native_pair P i j s hi hj hj0 hi0 hs Z hs0 c hc h hij).1).trans hr'.symm))

lemma diag_braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three true false false trivial hi hj rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three true false false trivial hi hj rfl) Z := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs.symm
    exact Prod.ext rfl he2
  erw [left_diag_route P i j s hi hj hj0 hi0 hs Z ν _ hij,
    right_route P i j s hi hj hj0 hi0 hs Z ν _ hij]
  have hu := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false true false hj0 trivial hi0 hs Z
  have ht := P.distinctReservoirSource_obj ν i j i s hj0 hi0 hs Z
  have hF := AdjacentReservoirReverseComparison.left_first P i j s hj0 hi0 hs Z ν c L hij
  have hG := P.distinctReservoir_right ν i j i s hj0 hi0 hi hj hs c L Z hij.symm
  have hD := heq_of_eq (target_diag P i j s hi hj Z ν c L)
  have hS := source_diag P i j s hj0 hi0 hs Z ν c L
  simp only [Functor.map_neg, Functor.map_comp] at hS
  have hl := comp_common_grid_heq hu rfl rfl (comp_common_grid_heq hu ht rfl hF hG) hD
  have hr := comp_common_grid_heq hu hu rfl hS (comp_common_grid_heq hu ht rfl hF hG)
  have hr' := (heq_of_eq (Category.assoc _ _ _)).trans hr
  exact eq_of_heq (hl.trans ((heq_of_eq
    (native_pair P i j s hi hj hj0 hi0 hs Z hs0 c hc h hij).2).trans hr'.symm))

lemma square_braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial e)
      (SPath.three true false false trivial hi hj e') Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial e)
      (SPath.three true false false trivial hi hj e') Z := by
  subst e'
  exact square_braid_entry P i j s hi hj hj0 hi0 e Z ν c L hc h hij

lemma diag_braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 e)
      (SPath.three true false false trivial hi hj e') Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 e)
      (SPath.three true false false trivial hi hj e') Z := by
  subst e'
  exact diag_braid_entry P i j s hi hj hj0 hi0 e Z ν c L hc h hij

include hj0 hi0 in
/-- Exhaustive opposite adjacent block, deriving the other reservoir order. -/
lemma braid_block (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up j, up i, up i]) s t)
    (q : SPath (wd D ν [up i, up i, up j]) s t)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν p q Z =
      braidRight (P.swappedGens c L) j i i ν p q Z := by
  obtain ⟨hi, hj⟩ := AdjacentReservoirSquareBlock.opposite_valid j i s hj0 hi0 hij.symm
  have hs : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) =
      nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) := by
    simp only [nextSector, tsub_right_comm]
  have e' := hs.trans e
  rcases adjacentPost_jii_cases hij hj0 hi0 e e p with hp | hp <;>
    rcases adjacentPost_iij_cases hij hi hj e' e' q with hq | hq
  · subst p q
    exact AdjacentReservoirReverseCoefficient.braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij
  · subst p q
    exact square_braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij
  · subst p q
    exact AdjacentReservoirReverseComparison.braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hij
  · subst p q
    exact diag_braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij

end AdjacentReservoirReverseBlock
end OddMath.QuiverHecke.SwappedAssembly

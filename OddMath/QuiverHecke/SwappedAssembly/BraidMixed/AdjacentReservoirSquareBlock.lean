/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReservoirReverse
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirComparison

/-! The adjacent-equal two-reservoir square entry and complete iij to jii block
of the Brundan–Ellis braid relation. -/
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
namespace AdjacentReservoirSquareBlock
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s))))

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

lemma square_left_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj hs
    let a : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three true false false trivial hi hj hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three true false false trivial hj0 hi0 rfl
    let m : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 rfl
    braidLeft G i i j ν n m Y =
      (crossEntry G ν [] i i [up j] n a Y ≫ crossEntry G ν [up i] i j [] a b Y) ≫
        crossEntry G ν [] i j [up i] b m Y := by
  classical
  dsimp only
  have hr := P.crossEntry_left_three_zero G ν i j i false false false true true false
    (by decide) hi hj hj0 trivial trivial hi0 hs rfl Y
  have hg := crossEntry_right_eq_zero G ν i i j false true (by decide)
    hi trivial (SPath.two true false trivial hj hs) (SPath.two false false hj0 hi0 rfl) Y
  unfold braidLeft
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 hs rfl]
  erw [adjacentPost_iij_sum hij hi hj hs hs, adjacentPost_iij_sum hij hi hj hs hs]
  exact square_route _ _ _ _ _ _ _ _ hr hg

lemma square_right_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj hs
    let a : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial rfl
    let m : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 rfl
    braidRight G i i j ν n m Y =
      (crossEntry G ν [up i] i j [] n a Y ≫ crossEntry G ν [] i j [up i] a b Y) ≫
        crossEntry G ν [up j] i i [] b m Y := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i i j false true (by decide)
    hi trivial (SPath.two true false trivial hj hs) (SPath.two false false hj0 hi0 rfl) Y
  have hg := P.crossEntry_left_three_zero G ν i j i false false false true true false
    (by decide) hi hj hj0 trivial trivial hi0 hs rfl Y
  unfold braidRight
  erw [adjacentPost_jii_sum hij hj0 hi0 rfl rfl]
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 hs rfl, adjacentPost_iji_sum hij hi hj hj0 hi0 hs rfl]
  exact route_right _ _ _ _ _ _ _ _ hf hg

private lemma square {C : Type u} [Category C] [Preadditive C]
    {A M N T U V : C} (E : A ≅ M) (J : M ≅ N) (H : T ≅ U) (K : U ≅ V)
    (F : A ⟶ T) (f : N ⟶ V) (a : M ⟶ M) (b : V ⟶ V)
    (hr : F ≫ H.hom ≫ K.hom = E.hom ≫ J.hom ≫ f)
    (ha : (J.inv ≫ a ≫ J.hom) ≫ f = f ≫ b) :
    ((-(a ≫ a ≫ E.inv)) ≫ F) ≫ H.hom =
      (J.hom ≫ f) ≫ (-(b ≫ b ≫ K.inv)) := by
  have hr' : E.inv ≫ F ≫ H.hom = J.hom ≫ f ≫ K.inv := by
    have he := congrArg (fun g => E.inv ≫ g ≫ K.inv) hr
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using he
  have ha' : a ≫ J.hom ≫ f = J.hom ≫ f ≫ b := by
    have he := congrArg (fun g => J.hom ≫ g) ha
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  congr 1
  rw [hr']
  rw [← Category.assoc J.hom f, ← Category.assoc a (J.hom ≫ f), ha']
  simp only [Category.assoc]
  rw [← Category.assoc J.hom f, ← Category.assoc a (J.hom ≫ f), ha']
  simp only [Category.assoc]

lemma square_native
    (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let E := P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y))
    let J := RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)
    let H := RepeatedOuterPost.firstIso P i j s hj0 hi0 Y
    let K := (P.step (true, j) false s hj0).mapIso
      (P.mixedJ i i (nextSector (true, j) false s) hi0 Y)
    let a := c.a i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y))
    let b := (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 Y)
    let F := RepeatedOuterPre.probeReservoirCross P i j s hi hj hj0 hi0 hs Y
    let f := RepeatedOuterPre.reservoirCross P i j s hi hj hj0 hi0 Y hs0
    ((-(a ≫ a ≫ E.inv)) ≫ F) ≫ H.hom = (J.hom ≫ f) ≫ (-(b ≫ b ≫ K.inv)) := by
  dsimp only
  apply square
  · exact eq_of_heq (P.postCrossNe_mixedJ_pair_heq i i j s hi hj hj0 hi0 hs0 hs Y)
  · exact RepeatedOuterPre.coeff_slide P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij

lemma square_last (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three true false false trivial hj0 hi0 rfl)
      (SPath.three false true false hj0 trivial hi0 rfl) Y =
    (RepeatedOuterPost.firstIso P i j s hj0 hi0 Y).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i j i
    (SPath.two true false trivial hj0 rfl) (SPath.two false true hj0 trivial rfl)
    (.cons _ false _ hi0 (.nil _)) Y).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  rfl

lemma square_braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj hs)
      (SPath.three false true false hj0 trivial hi0 rfl) Y =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj hs)
      (SPath.three false true false hj0 trivial hi0 rfl) Y := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs
    exact Prod.ext rfl he2
  erw [square_left_route P i j s hi hj hj0 hi0 hs Y ν _ hij,
    square_right_route P i j s hi hj hj0 hi0 hs Y ν _ hij]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true false hi trivial hj hs Y
  have ha := P.distinctReservoirSource_obj ν i i j s hi hj hs Y
  have hb := P.distinctReservoirTarget_obj ν i i j s hi hj hs Y
  have hl₁ := RepeatedOuterReservoirReverse.right_middle P i j s hi hj hs Y ν c L
  have hl₂ := P.distinctReservoir_right ν i i j s hi hj hj0 hi0 hs c L Y hij
  have hl₃ := heq_of_eq (square_last P i j s hj0 hi0 Y ν c L hij)
  have hr₁ := AdjacentReservoirPreCoefficient.mixed_edge P i j s hi hj hs Y ν c L hij
  have hr₂ := RepeatedOuterPre.left_first P i j s hi hj hj0 hi0 hs Y hs0 ν c L hij
  have hm := RepeatedOuterReservoirReverse.left_middle P i j s hj0 hi0 Y ν c L
  simp only [Functor.map_neg, Functor.map_comp] at hm
  have hr₃ := heq_of_eq hm
  have hl := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn ha rfl hl₁ hl₂) hl₃
  have hr := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn hb rfl hr₁ hr₂) hr₃
  exact eq_of_heq (hl.trans ((heq_of_eq
    (square_native P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij)).trans hr.symm))

lemma square_braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj e)
      (SPath.three false true false hj0 trivial hi0 e') Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj e)
      (SPath.three false true false hj0 trivial hi0 e') Z := by
  subst e'
  exact square_braid_entry P i j s hi hj hj0 hi0 e Z ν c L hc h hij

include hi hj in
lemma opposite_valid (hij : i ≠ j) :
    StepValid (true, j) false s ∧ StepValid (true, i) false (nextSector (true, j) false s) := by
  constructor
  · simpa [StepValid, nextSector, hij, Ne.symm hij] using hj
  · simpa [StepValid, nextSector, hij, Ne.symm hij] using hi

include hi hj in
/-- All four entries of the adjacent-equal two-reservoir block. The opposite
reservoir order and its terminal endpoint are derived from the source order. -/
lemma braid_block (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z := by
  obtain ⟨hj0, hi0⟩ := opposite_valid i j s hi hj hij
  have hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
      nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) := by
    simp only [nextSector, tsub_right_comm]
  have e' := hs.trans e
  rcases adjacentPost_iij_cases hij hi hj e e p with hp | hp <;>
    rcases adjacentPost_jii_cases hij hj0 hi0 e' e' q with hq | hq
  · subst p q
    exact AdjacentReservoirPreCoefficient.braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij
  · subst p q
    exact square_braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij
  · subst p q
    exact P.adjacentReservoir_comparison_braid_transport ν i j s hi hj hj0 hi0 e e' Z c L hij
  · subst p q
    exact AdjacentReservoirCoefficient.braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij

end AdjacentReservoirSquareBlock
end OddMath.QuiverHecke.SwappedAssembly

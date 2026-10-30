/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirReverseCoefficient

/-! The adjacent-equal two-reservoir entry Rj Pi Ri to Ri Pi Rj
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
namespace AdjacentReservoirReverseComparison
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (Z : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))

private lemma route_left {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hg : g₁₀ = 0) (hr : r₁ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₀ ≫ g₀₀) ≫ r₀ := by
  rw [hg, hr]
  simp only [Limits.comp_zero, add_zero]


private lemma route_reverse {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hf : f₀ = 0) (hg : g₁₀ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₁ ≫ g₁₁) ≫ r₁ := by
  rw [hf, hg]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero, zero_add]

lemma left_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 hs
    let a : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three true false false trivial hj0 hi0 hs
    let b : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three true false false trivial hi hj rfl
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj rfl
    braidLeft G j i i ν n m Z =
      (crossEntry G ν [] j i [up i] n a Z ≫ crossEntry G ν [up i] j i [] a b Z) ≫
        crossEntry G ν [] i i [up j] b m Z := by
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

lemma right_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 hs
    let a : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj rfl
    braidRight G j i i ν n m Z =
      (crossEntry G ν [up j] i i [] n a Z ≫ crossEntry G ν [] j i [up i] a b Z) ≫
        crossEntry G ν [up i] j i [] b m Z := by
  classical
  dsimp only
  have hg := P.crossEntry_left_three_zero G ν j i i false true false false false true
    (by decide) hj0 trivial hi hj hi0 trivial hs rfl Z
  have hr := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hi (SPath.two false false hj0 hi0 hs) (SPath.two true false trivial hj rfl) Z
  unfold braidRight
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 rfl hs]
  erw [adjacentPost_jii_sum hij hj0 hi0 hs hs, adjacentPost_jii_sum hij hj0 hi0 hs hs]
  exact route_left _ _ _ _ _ _ _ _ hg hr

private lemma rectangle {C : Type u} [Category C]
    {A M N T U V : C} (E : A ≅ M) (J : M ≅ N) (H : T ≅ U) (K : U ≅ V)
    (F : T ⟶ A) (f : V ⟶ N) (Q₀ : M ⟶ M) (Q : T ⟶ T)
    (hr : F ≫ E.hom ≫ J.hom = H.hom ≫ K.hom ≫ f)
    (hq : Q ≫ F = F ≫ (E.hom ≫ Q₀ ≫ E.inv)) :
    ((H.inv ≫ Q) ≫ F) ≫ E.hom = (K.hom ≫ f) ≫ (J.inv ≫ Q₀) := by
  have hr' : H.inv ≫ F ≫ E.hom = K.hom ≫ f ≫ J.inv := by
    have he := congrArg (fun g => H.inv ≫ g ≫ J.inv) hr
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using he
  simp only [Category.assoc]
  rw [← Category.assoc Q F, hq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc F E.hom, ← Category.assoc H.inv (F ≫ E.hom), hr']
  simp only [Category.assoc]

lemma native_entry
    (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (hij : i ≠ j) :
    let E := P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj Z)
    let J := RepeatedOuterPre.rightIso P i j s hi hj Z
    let H := RepeatedOuterPost.firstIso P i j s hj0 hi0 (hs ▸ Z)
    let K := (P.step (true, j) false s hj0).mapIso
      (P.mixedJ i i (nextSector (true, j) false s) hi0 (hs ▸ Z))
    let Q₀ := (P.step (true, i) false s hi).map (P.mixedQ i j (nextSector (true, i) false s) hj Z)
    let Q := P.mixedQ i j s hj0 (P.distinctReservoirRest i j i s hi0 (hs ▸ Z))
    let F := RepeatedOuterPost.reservoirCross P i j s hj0 hi0 hi hj hs Z
    let f := RepeatedOuterPre.reservoirBack P i j s hi hj hj0 hi0 hs0 Z
    ((H.inv ≫ Q) ≫ F) ≫ E.hom = (K.hom ≫ f) ≫ (J.inv ≫ Q₀) := by
  dsimp only
  apply rectangle
  · exact eq_of_heq (P.postCrossNe_mixedJ_pair_heq i j i s hj0 hi0 hi hj hs0.symm hs Z)
  · exact (P.postCrossNe_qExpr_outer i j i s hj0 hi0 hi hj hij.symm hs Z).trans
      (congrArg (fun g => RepeatedOuterPost.reservoirCross P i j s hj0 hi0 hi hj hs Z ≫ g)
        (P.distinctReservoirFirstIso_conj_mixedQ i i j s hi hj Z).symm)

lemma left_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three true false false trivial hj0 hi0 hs) Z)
      ((RepeatedOuterPost.firstIso P i j s hj0 hi0 (hs ▸ Z)).inv ≫
        P.mixedQ i j s hj0 (P.distinctReservoirRest i j i s hi0 (hs ▸ Z))) := by
  generalize ht : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t at Z hs
  subst hs
  exact heq_of_eq (RepeatedOuterReservoirReverse.left_last P i j s hj0 hi0 Z ν c L hij)

lemma left_last (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false false trivial hi hj rfl)
      (SPath.three false true false hi trivial hj rfl) Z =
      (P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj Z)).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two true false trivial hi rfl) (SPath.two false true hi trivial rfl)
    (.cons _ false _ hj (.nil _)) Z).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma right_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three false false true hj0 hi0 trivial hs) Z)
      ((P.step (true, j) false s hj0).map
        (P.mixedJ i i (nextSector (true, j) false s) hi0 (hs ▸ Z)).hom) := by
  generalize ht : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t at Z hs
  subst hs
  apply heq_of_eq
  refine (crossEntry_right (P.swappedGens c L) ν j i i false hj0
    (SPath.two true false trivial hi0 rfl) (SPath.two false true hi0 trivial rfl) Z).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three false true false hi trivial hj rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 hs)
      (SPath.three false true false hi trivial hj rfl) Z := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs.symm
    exact Prod.ext rfl he2
  erw [left_route P i j s hi hj hj0 hi0 hs Z ν _ hij,
    right_route P i j s hi hj hj0 hi0 hs Z ν _ hij]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false true false hj0 trivial hi0 hs Z
  have ha := P.distinctReservoirSource_obj ν i j i s hj0 hi0 hs Z
  have hb := P.distinctReservoirTarget_obj ν i j i s hj0 hi0 hs Z
  have hl₁ := left_first P i j s hj0 hi0 hs Z ν c L hij
  have hl₂ := P.distinctReservoir_right ν i j i s hj0 hi0 hi hj hs c L Z hij.symm
  have hl₃ := heq_of_eq (left_last P i j s hi hj Z ν c L)
  have hr₁ := right_first P i j s hj0 hi0 hs Z ν c L
  have hr₂ := P.repeatedReservoir_left ν i j s hj0 hi0 hi hj hs0.symm hs c L Z hij
  have hr₃ := heq_of_eq (RepeatedOuterPre.right_first P i j s hi hj Z ν c L hij)
  have hl := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn ha rfl hl₁ hl₂) hl₃
  have hr := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn hb rfl hr₁ hr₂) hr₃
  exact eq_of_heq (hl.trans ((heq_of_eq
    (native_entry P i j s hi hj hj0 hi0 hs Z hs0 hij)).trans hr.symm))

lemma braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 e)
      (SPath.three false true false hi trivial hj e') Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false true false hj0 trivial hi0 e)
      (SPath.three false true false hi trivial hj e') Z := by
  subst e'
  exact braid_entry P i j s hi hj hj0 hi0 e Z ν c L hij

lemma braid_entry_path (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up j, up i, up i]) s t)
    (q : SPath (wd D ν [up i, up i, up j]) s t)
    (hp : p = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false true false hj0 trivial hi0 e)
    (hq : q = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
      false true false hi trivial hj e')
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν p q Z =
      braidRight (P.swappedGens c L) j i i ν p q Z := by
  subst p q
  exact braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hij

end AdjacentReservoirReverseComparison
end OddMath.QuiverHecke.SwappedAssembly

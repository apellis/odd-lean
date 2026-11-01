/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirPreCoefficient

/-! The repeated-outer two-reservoir entry Ri Rj Pi to Pi Rj Ri. -/
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
namespace RepeatedOuterReservoirReverse
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s))))

private lemma coefficient_alg_commute (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (t : Sector I) (hv : StepValid (true, i) false t)
    (V : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
    {C : Type u} [Category C] [Preadditive C] [Linear k C] {Y : C}
    (φ : End (P.rpObj i i t hv V) →ₐ[k] End Y) (f : End Y)
    (hx : φ (P.rpPreDot i t hv V) ≫ f = f ≫ φ (P.rpPreDot i t hv V))
    (hy : φ (P.rpPostDot i t hv V) ≫ f = f ≫ φ (P.rpPostDot i t hv V)) :
    φ (c.a i t hv V) ≫ f = f ≫ φ (c.a i t hv V) := by
  have hmap (a b : End (P.rpObj i i t hv V)) : φ (a ≫ b) = φ a ≫ φ b :=
    φ.map_mul b a
  by_cases hi : D.parity i = 0
  · have ha := congrArg φ (hc.even i hi t hv V).1
    have hb := congrArg φ (hc.even i hi t hv V).2
    simp only [hmap, map_sub, show φ (𝟙 _) = 𝟙 _ from φ.map_one] at ha hb
    simpa only [one_smul] using signed_inverse_difference_transport
      _ _ _ _ _ _ f (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hy.trans (one_smul _ _).symm) ha hb
  · have hi' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hi
    have ha := congrArg φ (hc.odd i hi' t hv V).1
    simp only [hmap, map_sub] at ha
    have hd : (P.crossDenom h i t hv V : End (P.rpObj i i t hv V)) =
        P.rpPreDot i t hv V ≫ P.rpPreDot i t hv V -
          P.rpPostDot i t hv V ≫ P.rpPostDot i t hv V := by
      simp [crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg φ hd
    simp only [hmap, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport
      _ _ _ _ _ _ f (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hy.trans (one_smul _ _).symm) ha ha
      (Units.map φ.toMonoidHom (P.crossDenom h i t hv V)) hd'


lemma mixedQ_coefficient_comm (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs)
    (Z : P.H (nextSector (true, j) false
      (nextSector (true, i) false (nextSector (true, i) true s)))) :
    c.a i s hi (RepeatedOuterPre.rest P i j s hj Z) ≫
      (P.step (true, i) false s hi).map
        (P.mixedQ i j (nextSector (true, i) false s) hj Z) =
    (P.step (true, i) false s hi).map
        (P.mixedQ i j (nextSector (true, i) false s) hj Z) ≫
      c.a i s hi (RepeatedOuterPre.rest P i j s hj Z) := by
  apply coefficient_alg_commute P i c hc h s hi _ (AlgHom.id k _)
  · have he := congrArg (P.step (true, i) false s hi).map
      (P.mixedQ_comm i j (nextSector (true, i) false s) hj Z).2
    simp only [Functor.map_comp] at he
    exact he
  · have he := (P.dotDiag_supernatural i false s hi).naturality
      ((P.mixedQ_supernatural i j (nextSector (true, i) false s) hj).mem Z)
    simp only [mul_zero, Supercategory.sign_zero, one_smul] at he
    exact he.symm

private lemma weighted_square {C : Type u} [Category C] [Preadditive C]
    {A M N T U V : C} (E : A ≅ M) (J : M ≅ N) (H : T ≅ U) (K : U ≅ V)
    (F : A ⟶ T) (f : N ⟶ V) (a Q₀ : M ⟶ M) (b : V ⟶ V) (Q : T ⟶ T)
    (hr : F ≫ H.hom ≫ K.hom = E.hom ≫ J.hom ≫ f)
    (ha : (J.inv ≫ a ≫ J.hom) ≫ f = f ≫ b)
    (hq : (E.hom ≫ Q₀ ≫ E.inv) ≫ F = F ≫ Q)
    (hc : a ≫ Q₀ = Q₀ ≫ a) :
    (f ≫ (-(b ≫ b ≫ K.inv))) ≫ (H.inv ≫ Q) =
      ((J.inv ≫ Q₀) ≫ (-(a ≫ a ≫ E.inv))) ≫ F := by
  have hr' : f ≫ K.inv ≫ H.inv = J.inv ≫ E.inv ≫ F := by
    have he := congrArg (fun g => J.inv ≫ E.inv ≫ g ≫ K.inv ≫ H.inv) hr
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using he.symm
  have ha' : f ≫ b = J.inv ≫ a ≫ J.hom ≫ f := by
    simpa only [Category.assoc] using ha.symm
  have hq' : E.inv ≫ F ≫ Q = Q₀ ≫ E.inv ≫ F := by
    have he := congrArg (fun g => E.inv ≫ g) hq
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he.symm
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  congr 1
  rw [← Category.assoc f b, ha']
  simp only [Category.assoc]
  rw [← Category.assoc f b, ha']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc f K.inv, ← Category.assoc (f ≫ K.inv) H.inv, Category.assoc f K.inv, hr']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hq']
  rw [← Category.assoc a Q₀, hc]
  simp only [Category.assoc]
  rw [← Category.assoc a Q₀, hc]
  simp only [Category.assoc]

lemma weighted_entry
    (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let E := P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y))
    let J := RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)
    let H := RepeatedOuterPost.firstIso P i j s hj0 hi0 Y
    let K := (P.step (true, j) false s hj0).mapIso
      (P.mixedJ i i (nextSector (true, j) false s) hi0 Y)
    let a := c.a i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y))
    let b := (P.step (true, j) false s hj0).map
      (c.a i (nextSector (true, j) false s) hi0 Y)
    let Q₀ := (P.step (true, i) false s hi).map
      (P.mixedQ i j (nextSector (true, i) false s) hj (hs ▸ Y))
    let Q := P.mixedQ i j s hj0 (P.distinctReservoirRest i j i s hi0 Y)
    let F := RepeatedOuterPre.probeReservoirCross P i j s hi hj hj0 hi0 hs Y
    let f := RepeatedOuterPre.reservoirCross P i j s hi hj hj0 hi0 Y hs0
    (f ≫ (-(b ≫ b ≫ K.inv))) ≫ (H.inv ≫ Q) =
      ((J.inv ≫ Q₀) ≫ (-(a ≫ a ≫ E.inv))) ≫ F := by
  dsimp only
  apply weighted_square
  · exact eq_of_heq (P.postCrossNe_mixedJ_pair_heq i i j s hi hj hj0 hi0 hs0 hs Y)
  · exact RepeatedOuterPre.coeff_slide P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij
  · exact (congrArg (fun g => g ≫ RepeatedOuterPre.probeReservoirCross P i j s hi hj hj0 hi0 hs Y)
      (P.distinctReservoirFirstIso_conj_mixedQ i i j s hi hj (hs ▸ Y))).trans
      (P.postCrossNe_qExpr_inner i i j s hi hj hj0 hi0 hij hs Y)
  · exact mixedQ_coefficient_comm P i j s hi hj c hc h (hs ▸ Y)

private lemma route {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hf : f₁ = 0) (hr : r₀ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₀ ≫ g₀₁) ≫ r₁ := by
  rw [hf, hr]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero, zero_add]

lemma left_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial rfl
    let d : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false true false hj0 trivial hi0 rfl
    let m : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three true false false trivial hj0 hi0 rfl
    braidLeft G i j i ν n m Y =
      (crossEntry G ν [] i j [up i] n b Y ≫ crossEntry G ν [up j] i i [] b d Y) ≫
        crossEntry G ν [] j i [up i] d m Y := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν i j i false false false true true false
    (by decide) hi hj hj0 trivial trivial hi0 hs rfl Y
  have hr := P.crossEntry_left_three_zero G ν j i i false false true false true false
    (by decide) hj0 hi0 trivial hj0 trivial hi0 rfl rfl Y
  unfold braidLeft
  erw [adjacentPost_jii_sum hij hj0 hi0 rfl rfl]
  erw [adjacentPost_jii_sum hij hj0 hi0 rfl rfl, adjacentPost_jii_sum hij hj0 hi0 rfl rfl]
  exact route _ _ _ _ _ _ _ _ hf hr

lemma right_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial hs
    let b : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj hs
    let d : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three true false false trivial hi hj hs
    let m : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three true false false trivial hj0 hi0 rfl
    braidRight G i j i ν n m Y =
      (crossEntry G ν [up i] j i [] n b Y ≫ crossEntry G ν [] i i [up j] b d Y) ≫
        crossEntry G ν [up i] i j [] d m Y := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i j i false true (by decide)
    hi trivial (SPath.two false true hj trivial hs) (SPath.two false false hi hj hs) Y
  have hr := crossEntry_right_eq_zero G ν i i j false true (by decide)
    hi trivial (SPath.two true false trivial hj hs) (SPath.two false false hj0 hi0 rfl) Y
  unfold braidRight
  erw [adjacentPost_iij_sum hij hi hj hs hs]
  erw [adjacentPost_iij_sum hij hi hj hs hs, adjacentPost_iij_sum hij hi hj hs hs]
  exact route _ _ _ _ _ _ _ _ hf hr

lemma right_middle (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true false hi trivial hj hs)
      (SPath.three true false false trivial hi hj hs) Y)
      (-(c.a i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y)) ≫
        c.a i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y)) ≫
        (P.mixedJ i i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y))).inv)) := by
  generalize ht : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t at Y hs
  subst hs
  apply heq_of_eq
  refine (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two false true hi trivial rfl) (SPath.two true false trivial hi rfl)
    (.cons _ false _ hj (.nil _)) Y).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma left_middle (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false false true hj0 hi0 trivial rfl)
      (SPath.three false true false hj0 trivial hi0 rfl) Y =
      (P.step (true, j) false s hj0).map
        (-(c.a i (nextSector (true, j) false s) hi0 Y ≫
          c.a i (nextSector (true, j) false s) hi0 Y ≫
          (P.mixedJ i i (nextSector (true, j) false s) hi0 Y).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i false hj0
    (SPath.two false true hi0 trivial rfl) (SPath.two true false trivial hi0 rfl) Y).trans ?_
  erw [swappedGens_cross_self]
  rfl

lemma left_last (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three false true false hj0 trivial hi0 rfl)
      (SPath.three true false false trivial hj0 hi0 rfl) Y =
    (RepeatedOuterPost.firstIso P i j s hj0 hi0 Y).inv ≫
      P.mixedQ i j s hj0 (P.distinctReservoirRest i j i s hi0 Y) := by
  refine (crossEntry_left (P.swappedGens c L) ν j i i
    (SPath.two false true hj0 trivial rfl) (SPath.two true false trivial hj0 rfl)
    (.cons _ false _ hi0 (.nil _)) Y).trans ?_
  apply eq_of_heq
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  rfl

lemma right_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false false true hi hj trivial hs)
      (SPath.three false true false hi trivial hj hs) Y)
      ((RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)).inv ≫
        (P.step (true, i) false s hi).map
          (P.mixedQ i j (nextSector (true, i) false s) hj (hs ▸ Y))) := by
  generalize ht : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t at Y hs
  subst hs
  exact heq_of_eq (RepeatedOuterPre.right_first P i j s hi hj Y ν c L hij)

lemma braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial hs)
      (SPath.three true false false trivial hj0 hi0 rfl) Y =
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial hs)
      (SPath.three true false false trivial hj0 hi0 rfl) Y := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs
    exact Prod.ext rfl he2
  erw [left_route P i j s hi hj hj0 hi0 hs Y ν _ hij,
    right_route P i j s hi hj hj0 hi0 hs Y ν _ hij]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false false true hi hj trivial hs Y
  have hb := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true false hi trivial hj hs Y
  have hd := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    true false false trivial hi hj hs Y
  have hl₁ := RepeatedOuterPre.left_first P i j s hi hj hj0 hi0 hs Y hs0 ν c L hij
  have hm := left_middle P i j s hj0 hi0 Y ν c L
  simp only [Functor.map_neg, Functor.map_comp] at hm
  have hl₂ := heq_of_eq hm
  have hl₃ := heq_of_eq (left_last P i j s hj0 hi0 Y ν c L hij)
  have hr₁ := right_first P i j s hi hj hs Y ν c L hij
  have hr₂ := right_middle P i j s hi hj hs Y ν c L
  have hr₃ := P.distinctReservoir_right ν i i j s hi hj hj0 hi0 hs c L Y hij
  have hl := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn rfl rfl hl₁ hl₂) hl₃
  have hr := comp_common_grid_heq hn hd rfl (comp_common_grid_heq hn hb hd hr₁ hr₂) hr₃
  exact eq_of_heq (hl.trans ((heq_of_eq
    (weighted_entry P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij)).trans hr.symm))

lemma braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial e)
      (SPath.three true false false trivial hj0 hi0 e') Z =
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial e)
      (SPath.three true false false trivial hj0 hi0 e') Z := by
  subst e'
  exact braid_entry P i j s hi hj hj0 hi0 e Z ν c L hc h hij

lemma braid_entry_path (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up i, up j, up i]) s t)
    (q : SPath (wd D ν [up i, up j, up i]) s t)
    (hp : p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hi hj trivial e)
    (hq : q = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true false false trivial hj0 hi0 e')
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν p q Z =
      braidRight (P.swappedGens c L) i j i ν p q Z := by
  subst p q
  exact braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij

end RepeatedOuterReservoirReverse
end OddMath.QuiverHecke.SwappedAssembly

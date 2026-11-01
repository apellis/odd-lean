/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirSquareBlock

/-! The adjacent-equal two-reservoir entry Rj Ri Pi to Ri Pi Rj
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
namespace AdjacentReservoirReverseCoefficient
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

private lemma route_right {C : Type u} [Category C] [Preadditive C]
    {A B₀ B₁ C₀ C₁ T : C} (f₀ : A ⟶ B₀) (f₁ : A ⟶ B₁)
    (g₀₀ : B₀ ⟶ C₀) (g₁₀ : B₁ ⟶ C₀) (g₀₁ : B₀ ⟶ C₁) (g₁₁ : B₁ ⟶ C₁)
    (r₀ : C₀ ⟶ T) (r₁ : C₁ ⟶ T) (hf : f₁ = 0) (hg : g₀₁ = 0) :
    (f₀ ≫ g₀₀ + f₁ ≫ g₁₀) ≫ r₀ + (f₀ ≫ g₀₁ + f₁ ≫ g₁₁) ≫ r₁ =
      (f₀ ≫ g₀₀) ≫ r₀ := by
  rw [hf, hg]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero]


lemma left_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj rfl
    braidLeft G j i i ν n m Z =
      (crossEntry G ν [] j i [up i] n b Z ≫ crossEntry G ν [up i] j i [] b m Z) ≫
        crossEntry G ν [] i i [up j] m m Z := by
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

lemma right_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    let m : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj rfl
    braidRight G j i i ν n m Z =
      (crossEntry G ν [up j] i i [] n n Z ≫ crossEntry G ν [] j i [up i] n b Z) ≫
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

private lemma native {C : Type u} [Category C]
    {M N V : C} (J : M ≅ N) (f : V ⟶ N) (a Q : M ⟶ M) (b : V ⟶ V)
    (hs : b ≫ f = f ≫ (J.inv ≫ a ≫ J.hom)) (hc : a ≫ Q = Q ≫ a) :
    (f ≫ (J.inv ≫ Q)) ≫ a = (b ≫ f) ≫ (J.inv ≫ Q) := by
  rw [hs]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hc]

lemma native_entry
    (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let J := RepeatedOuterPre.rightIso P i j s hi hj Z
    let f := RepeatedOuterPre.reservoirBack P i j s hi hj hj0 hi0 hs0 Z
    let a := c.a i s hi (RepeatedOuterPre.rest P i j s hj Z)
    let Q := (P.step (true, i) false s hi).map (P.mixedQ i j (nextSector (true, i) false s) hj Z)
    let b := (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Z))
    (f ≫ (J.inv ≫ Q)) ≫ a = (b ≫ f) ≫ (J.inv ≫ Q) := by
  dsimp only
  apply native
  · exact RepeatedOuterPre.coeff_slide_back P i j s hi hj hj0 hi0 hs.symm hs0 Z c hc h hij
  · exact RepeatedOuterReservoirReverse.mixedQ_coefficient_comm P i j s hi hj c hc h Z

lemma source_diag (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false false true hj0 hi0 trivial hs)
      (SPath.three false false true hj0 hi0 trivial hs) Z)
      ((P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Z))) := by
  generalize ht : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t at Z hs
  subst hs
  exact heq_of_eq (RepeatedOuterPre.left_mid P i j s hj0 hi0 Z ν c L)

lemma braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial hs)
      (SPath.three false true false hi trivial hj rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial hs)
      (SPath.three false true false hi trivial hj rfl) Z := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs.symm
    exact Prod.ext rfl he2
  erw [left_route P i j s hi hj hj0 hi0 hs Z ν _ hij,
    right_route P i j s hi hj hj0 hi0 hs Z ν _ hij]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false false true hj0 hi0 trivial hs Z
  have hf := P.repeatedReservoir_left ν i j s hj0 hi0 hi hj hs0.symm hs c L Z hij
  have hJ := heq_of_eq (RepeatedOuterPre.right_first P i j s hi hj Z ν c L hij)
  have ha := heq_of_eq (RepeatedOuterPre.right_mid P i j s hi hj Z ν c L)
  have hb := source_diag P i j s hj0 hi0 hs Z ν c L
  have hl := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn rfl rfl hf hJ) ha
  have hr := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn hn rfl hb hf) hJ
  exact eq_of_heq (hl.trans ((heq_of_eq
    (native_entry P i j s hi hj hj0 hi0 hs Z hs0 c hc h hij)).trans hr.symm))

lemma braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial e)
      (SPath.three false true false hi trivial hj e') Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three false false true hj0 hi0 trivial e)
      (SPath.three false true false hi trivial hj e') Z := by
  subst e'
  exact braid_entry P i j s hi hj hj0 hi0 e Z ν c L hc h hij

lemma braid_entry_path (ν : X) {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up j, up i, up i]) s t)
    (q : SPath (wd D ν [up i, up i, up j]) s t)
    (hp : p = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hj0 hi0 trivial e)
    (hq : q = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
      false true false hi trivial hj e')
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν p q Z =
      braidRight (P.swappedGens c L) j i i ν p q Z := by
  subst p q
  exact braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij

end AdjacentReservoirReverseCoefficient
end OddMath.QuiverHecke.SwappedAssembly

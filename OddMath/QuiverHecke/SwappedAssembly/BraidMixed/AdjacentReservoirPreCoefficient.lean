/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirCoefficient

/-! The adjacent-equal two-reservoir entry Ri Pi Rj to Rj Ri Pi
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
namespace AdjacentReservoirPreCoefficient
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s))))

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
    let n : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial hs
    let m : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial rfl
    braidLeft G i i j ν n m Y =
      (crossEntry G ν [] i i [up j] n n Y ≫ crossEntry G ν [up i] i j [] n b Y) ≫
        crossEntry G ν [] i j [up i] b m Y := by
  classical
  dsimp only
  have hz := P.crossEntry_left_three_zero G ν i j i true false false false false true
    (by decide) trivial hj0 hj0 hi0 hi0 trivial rfl rfl Y
  have hf := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hi (SPath.two false false hi hj hs) (SPath.two false true hj trivial hs) Y
  unfold braidLeft
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 hs rfl]
  erw [adjacentPost_iij_sum hij hi hj hs hs, adjacentPost_iij_sum hij hi hj hs hs]
  exact route_left _ _ _ _ _ _ _ _ hf hz

lemma right_route (ν : X) (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up i, up j]) s _ := SPath.three false true false hi trivial hj hs
    let b : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial hs
    let m : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial rfl
    braidRight G i i j ν n m Y =
      (crossEntry G ν [up i] i j [] n b Y ≫ crossEntry G ν [] i j [up i] b m Y) ≫
        crossEntry G ν [up j] i i [] m m Y := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i i j false true (by decide)
    hi trivial (SPath.two true false trivial hj hs) (SPath.two false false hj0 hi0 rfl) Y
  have hz := P.crossEntry_left_three_zero G ν i j i false false false true true false
    (by decide) hi hj hj0 trivial trivial hi0 hs rfl Y
  unfold braidRight
  erw [adjacentPost_jii_sum hij hj0 hi0 rfl rfl]
  erw [adjacentPost_iji_sum hij hi hj hj0 hi0 hs rfl, adjacentPost_iji_sum hij hi hj hj0 hi0 hs rfl]
  exact route_right _ _ _ _ _ _ _ _ hf hz

lemma source_diag (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true false hi trivial hj hs)
      (SPath.three false true false hi trivial hj hs) Y)
      (c.a i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y))) := by
  generalize ht : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t at Y hs
  subst hs
  exact heq_of_eq (RepeatedOuterPre.right_mid P i j s hi hj Y ν c L)

lemma mixed_edge (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three false true false hi trivial hj hs)
      (SPath.three false false true hi hj trivial hs) Y)
      (RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)).hom := by
  generalize ht : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t at Y hs
  subst hs
  exact heq_of_eq (RepeatedOuterPre.right_last P i j s hi hj Y ν c L hij)

private lemma unconjugate_slide {C : Type u} [Category C]
    {A B T : C} (J : A ≅ B) (a : A ⟶ A) (f : B ⟶ T) (b : T ⟶ T)
    (h : (J.inv ≫ a ≫ J.hom) ≫ f = f ≫ b) :
    (a ≫ J.hom) ≫ f = (J.hom ≫ f) ≫ b := by
  have he := congrArg (fun g => J.hom ≫ g) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he

lemma native_entry
    (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    (c.a i s hi (RepeatedOuterPre.rest P i j s hj (hs ▸ Y)) ≫
      (RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)).hom) ≫
        RepeatedOuterPre.reservoirCross P i j s hi hj hj0 hi0 Y hs0 =
    ((RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)).hom ≫
      RepeatedOuterPre.reservoirCross P i j s hi hj hj0 hi0 Y hs0) ≫
        (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 Y) := by
  exact unconjugate_slide (RepeatedOuterPre.rightIso P i j s hi hj (hs ▸ Y)) _ _ _
    (RepeatedOuterPre.coeff_slide P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij)

lemma braid_entry (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj hs)
      (SPath.three false false true hj0 hi0 trivial rfl) Y =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj hs)
      (SPath.three false false true hj0 hi0 trivial rfl) Y := by
  have hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) hs
    exact Prod.ext rfl he2
  erw [left_route P i j s hi hj hj0 hi0 hs Y ν _ hij,
    right_route P i j s hi hj hj0 hi0 hs Y ν _ hij]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true false hi trivial hj hs Y
  have hb := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false false true hi hj trivial hs Y
  have hD := source_diag P i j s hi hj hs Y ν c L
  have hJ := mixed_edge P i j s hi hj hs Y ν c L hij
  have hF := RepeatedOuterPre.left_first P i j s hi hj hj0 hi0 hs Y hs0 ν c L hij
  have hE := heq_of_eq (RepeatedOuterPre.left_mid P i j s hj0 hi0 Y ν c L)
  have hl := comp_common_grid_heq hn hb rfl (comp_common_grid_heq hn hn hb hD hJ) hF
  have hr := comp_common_grid_heq hn rfl rfl (comp_common_grid_heq hn hb rfl hJ hF) hE
  exact eq_of_heq (hl.trans ((heq_of_eq
    (native_entry P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij)).trans hr.symm))

lemma braid_entry_transport (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj e)
      (SPath.three false false true hj0 hi0 trivial e') Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true false hi trivial hj e)
      (SPath.three false false true hj0 hi0 trivial e') Z := by
  subst e'
  exact braid_entry P i j s hi hj hj0 hi0 e Z ν c L hc h hij

lemma braid_entry_path (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t)
    (hp : p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
      false true false hi trivial hj e)
    (hq : q = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hj0 hi0 trivial e')
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z := by
  subst p q
  exact braid_entry_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij

end AdjacentReservoirPreCoefficient
end OddMath.QuiverHecke.SwappedAssembly

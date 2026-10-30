/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentSplitReduction

/-! # Adjacent mixed split-sector braid

The occupied split-sector matrix of Brundan–Ellis (1.9).
-/
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
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

section MatrixAlgebra
variable {C : Type*} [Category C] [Preadditive C]
  {a b q v : C} (J : b ≅ a) (K : v ≅ q) (A : End a) (B : End q)
  (M : a ⟶ q) (U : b ⟶ v)

omit [Preadditive C] in
/-- The opposite comparison rectangle only cancels comparison isomorphisms. -/
theorem splitMatrix_inv_rectangle (hJ : J.hom ≫ M = U ≫ K.hom) :
    J.inv ≫ U = M ≫ K.inv := by
  apply (cancel_mono K.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hJ, Iso.inv_hom_id_assoc]

/-- The square entry of the conjugate two-by-two crossing matrix. -/
theorem splitMatrix_square (hA : A ≫ M = M ≫ B)
    (hJ : J.hom ≫ M = U ≫ K.hom) :
    -(A ≫ A ≫ J.inv) ≫ U = M ≫ (-(B ≫ B ≫ K.inv)) := by
  have hU := splitMatrix_inv_rectangle J K M U hJ
  have hAA : (A ≫ A) ≫ M = M ≫ (B ≫ B) := by
    rw [Category.assoc, hA, ← Category.assoc, hA, Category.assoc]
  simp only [Preadditive.comp_neg]
  congr 1
  simp only [Category.assoc]
  rw [hU]
  simp only [← Category.assoc]
  rw [hAA]
  simp only [Category.assoc]

/-- The conjugate diagonal entry of the two-by-two crossing matrix. -/
theorem splitMatrix_conj (hA : A ≫ M = M ≫ B)
    (hJ : J.hom ≫ M = U ≫ K.hom) :
    -(J.hom ≫ A ≫ J.inv) ≫ U = U ≫ (-(K.hom ≫ B ≫ K.inv)) := by
  have hU := splitMatrix_inv_rectangle J K M U hJ
  simp only [Preadditive.comp_neg]
  congr 1
  simp only [Category.assoc]
  rw [hU, ← Category.assoc A M, hA]
  simp only [Category.assoc]
  rw [← Category.assoc J.hom M, hJ]
  simp only [Category.assoc]

end MatrixAlgebra
section CommonGrid
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (hs₀ : nextSector (true, j) true (nextSector (true, i) true s) =
    nextSector (true, i) true (nextSector (true, j) true s))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

include hs₀

/-- The raw square rectangle, before path endpoint transport. -/
theorem adjacentSplit_square_rectangle (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    (-(c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫ c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫ (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))).inv)) ≫ ((P.step (true, i) true s trivial).map
        ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
          P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
        P.adjacentMixedProbeCross i j s hR hs₀ Z) =
      (P.adjacentMixedMove i j s hR hs Z) ≫ (P.step (true, j) true s trivial).map
        (-(c.a i (nextSector (true, j) true s) hR Z ≫ c.a i (nextSector (true, j) true s) hR Z ≫ (P.mixedJ i i (nextSector (true, j) true s) hR Z).inv)) := by
  let J := P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))
  let K := (P.step (true, j) true s trivial).mapIso
    (P.mixedJ i i (nextSector (true, j) true s) hR Z)
  let A := c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))
  let B := (P.step (true, j) true s trivial).map (c.a i (nextSector (true, j) true s) hR Z)
  let M := P.adjacentMixedMove i j s hR hs Z
  let U := (P.step (true, i) true s trivial).map
    ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
      P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
    P.adjacentMixedProbeCross i j s hR hs₀ Z
  have hAM : A ≫ M = M ≫ B := P.adjacentMixedMove_coeff c hc h i j s hR hs Z hij
  have hJU : J.hom ≫ M = U ≫ K.hom := by
    simpa only [J, K, M, U, Functor.mapIso_hom, Category.assoc] using
      P.adjacentMixed_J_rectangle i j s hR hs₀ hs Z hij
  simpa only [J, K, A, B, M, U, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_neg, Functor.map_comp, Preadditive.neg_comp, Preadditive.comp_neg,
    Category.assoc] using
    splitMatrix_square J K A B M U hAM hJU

/-- The raw conj rectangle, before path endpoint transport. -/
theorem adjacentSplit_conj_rectangle (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    (-((P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))).hom ≫ c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫ (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))).inv)) ≫ ((P.step (true, i) true s trivial).map
        ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
          P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
        P.adjacentMixedProbeCross i j s hR hs₀ Z) =
      ((P.step (true, i) true s trivial).map
        ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
          P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
        P.adjacentMixedProbeCross i j s hR hs₀ Z) ≫ (P.step (true, j) true s trivial).map
        (-((P.mixedJ i i (nextSector (true, j) true s) hR Z).hom ≫ c.a i (nextSector (true, j) true s) hR Z ≫ (P.mixedJ i i (nextSector (true, j) true s) hR Z).inv)) := by
  let J := P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))
  let K := (P.step (true, j) true s trivial).mapIso
    (P.mixedJ i i (nextSector (true, j) true s) hR Z)
  let A := c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))
  let B := (P.step (true, j) true s trivial).map (c.a i (nextSector (true, j) true s) hR Z)
  let M := P.adjacentMixedMove i j s hR hs Z
  let U := (P.step (true, i) true s trivial).map
    ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
      P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
    P.adjacentMixedProbeCross i j s hR hs₀ Z
  have hAM : A ≫ M = M ≫ B := P.adjacentMixedMove_coeff c hc h i j s hR hs Z hij
  have hJU : J.hom ≫ M = U ≫ K.hom := by
    simpa only [J, K, M, U, Functor.mapIso_hom, Category.assoc] using
      P.adjacentMixed_J_rectangle i j s hR hs₀ hs Z hij
  simpa only [J, K, A, B, M, U, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_neg, Functor.map_comp, Preadditive.neg_comp, Preadditive.comp_neg,
    Category.assoc] using
    splitMatrix_conj J K A B M U hAM hJU

/-- The literal occupied split-sector J braid entry. -/
theorem adjacentSplit_braid_J (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three true false true trivial hR trivial rfl) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three true false true trivial hR trivial rfl) Z := by
  rw [P.adjacentSplit_left_q ν i j s hR c L hs Z hij,
    P.adjacentSplit_right_b ν i j s hR c L hs Z hij]
  have hA := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true true hR trivial trivial hs Z
  have hB := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    true false true trivial hR trivial hs Z
  have hS := P.adjacentSplit_source_J_heq ν i j s hR c L hs Z
  have hM := P.adjacentMixed_move_heq ν i j s hR c L hs Z hij
  have hU := P.adjacentSplit_move_heq ν i j s hR c L hs₀ hs Z hij
  have hT := heq_of_eq (P.adjacentSplit_target_J ν i j s hR c L Z)
  have hJ := P.adjacentMixed_J_rectangle_heq i j s hR hs₀ hs Z hij
  apply rectangle_of_heq hB hB hA rfl rfl hS hM hU hT
  exact hJ.trans (heq_of_eq (Category.assoc _ _ _).symm)

/-- The literal occupied split-sector square braid entry. -/
theorem adjacentSplit_braid_square (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs) (SPath.three true true false trivial trivial hR rfl) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs) (SPath.three true true false trivial trivial hR rfl) Z := by
  rw [P.adjacentSplit_left_v ν i j s hR c L hs Z hij,
    P.adjacentSplit_right_a ν i j s hR c L hs Z hij]
  have hA := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true true hR trivial trivial hs Z
  have hB := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    true false true trivial hR trivial hs Z
  apply rectangle_of_heq hA hA hB rfl rfl
    (P.adjacentSplit_source_square_heq ν i j s hR c L hs Z)
    (P.adjacentSplit_move_heq ν i j s hR c L hs₀ hs Z hij)
    (P.adjacentMixed_move_heq ν i j s hR c L hs Z hij)
    (heq_of_eq (P.adjacentSplit_target_square ν i j s hR c L Z))
  exact heq_of_eq (P.adjacentSplit_square_rectangle i j s hR c hs hs₀ Z hc h hij)

/-- The literal occupied split-sector conj braid entry. -/
theorem adjacentSplit_braid_conj (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three true true false trivial trivial hR rfl) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three true true false trivial trivial hR rfl) Z := by
  rw [P.adjacentSplit_left_v ν i j s hR c L hs Z hij,
    P.adjacentSplit_right_b ν i j s hR c L hs Z hij]
  have hA := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true true hR trivial trivial hs Z
  have hB := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    true false true trivial hR trivial hs Z
  apply rectangle_of_heq hB hB hB rfl rfl
    (P.adjacentSplit_source_conj_heq ν i j s hR c L hs Z)
    (P.adjacentSplit_move_heq ν i j s hR c L hs₀ hs Z hij)
    (P.adjacentSplit_move_heq ν i j s hR c L hs₀ hs Z hij)
    (heq_of_eq (P.adjacentSplit_target_conj ν i j s hR c L Z))
  exact heq_of_eq (P.adjacentSplit_conj_rectangle i j s hR c hs hs₀ Z hc h hij)

end CommonGrid

/-- The literal `i i j → j i i` braid on every path at the occupied split
endpoint. The repeated colour has one reservoir and one probe step, and the
other colour has a probe step. No uniqueness of either path type is assumed. -/
theorem adjacentSplit_braid (ν : X) (i j : I) (s : Sector I)
    (hR : StepValid (true, i) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (p : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))
    (q : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z := by
  have hs₀ : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s) := by
    simp only [nextSector, add_right_comm]
  have hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
      nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) := by
    simp only [nextSector, add_right_comm]
  rcases adjacentMixed_iij_cases hij hR hs hs p with rfl | rfl <;>
    rcases adjacentMixed_jii_cases hij hR rfl rfl q with rfl | rfl
  · exact P.adjacentMixed_braid ν i j s hR c L hs Z hc h hij
  · exact P.adjacentSplit_braid_square ν i j s hR c L hs hs₀ Z hc h hij
  · exact P.adjacentSplit_braid_J ν i j s hR c L hs hs₀ Z hij
  · exact P.adjacentSplit_braid_conj ν i j s hR c L hs hs₀ Z hc h hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

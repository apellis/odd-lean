/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseMatrix

/-! # Literal reverse adjacent split braid

All four entries of Brundan–Ellis (1.9) at the occupied reverse split endpoint.
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
section CommonGrid
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

include hs₀

/-- The literal reverse split diag entry. -/
theorem adjacentReverse_braid_diag (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three false true true hR trivial trivial rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three false true true hR trivial trivial rfl) Z := by
  rw [P.adjacentReverse_left_q (P.swappedGens c L) ν i j s hR hs Z hij,
    P.adjacentReverse_right_a (P.swappedGens c L) ν i j s hR hs Z hij]
  symm
  rw [Category.assoc]
  have hQ := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false true trivial hR trivial hs Z
  have hV := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  apply rectangle_of_heq hQ hQ hQ rfl rfl
    (P.adjacentReverse_source_diag_heq ν i j s c L hR hs Z)
    (P.adjacentReverse_move_heq ν i j s c L hR hs Z hij)
    (P.adjacentReverse_move_heq ν i j s c L hR hs Z hij)
    (P.adjacentReverse_target_diag_heq ν i j s c L hR Z)
  apply heq_of_eq
  have hr := (P.adjacentReverse_splitMatrix i j s hR hs₀ hs Z c hc h hij).1
  simpa only [Functor.map_neg, Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc] using hr

/-- The literal reverse split J entry. -/
theorem adjacentReverse_braid_J (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three true true false trivial trivial hR hs) (SPath.three false true true hR trivial trivial rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three true true false trivial trivial hR hs) (SPath.three false true true hR trivial trivial rfl) Z := by
  rw [P.adjacentReverse_left_v (P.swappedGens c L) ν i j s hR hs Z hij,
    P.adjacentReverse_right_a (P.swappedGens c L) ν i j s hR hs Z hij]
  symm
  rw [Category.assoc]
  have hQ := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false true trivial hR trivial hs Z
  have hV := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  apply rectangle_of_heq hV hV hQ rfl rfl
    (P.adjacentReverse_source_J_heq ν i j s c L hR hs Z)
    (P.adjacentReverse_move_heq ν i j s c L hR hs Z hij)
    (P.adjacentReverse_comparison_heq ν i j s c L hR hs₀ hs Z hij)
    (P.adjacentReverse_target_J_heq ν i j s c L hR Z)
  apply heq_of_eq
  have hr := (P.adjacentReverse_splitMatrix i j s hR hs₀ hs Z c hc h hij).2.1
  simpa only [Functor.map_neg, Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc] using hr

/-- Identify the source-square/comparison route on the common grid. -/
theorem adjacentReverse_square_left_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial hs) (SPath.three true true false trivial trivial hR hs) Z ≫
    (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true true false trivial trivial hR hs) (SPath.three true true false trivial trivial hR rfl) Z ≫
    crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three true true false trivial trivial hR rfl) (SPath.three true false true trivial hR trivial rfl) Z))
      ((P.step (true, j) true s trivial).map
      (-(c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
        c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
        (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv)) ≫
      (P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
        (P.step (true, i) true s trivial).map
          (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom)) := by
  have hQ := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false true trivial hR trivial hs Z
  have hV := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  have hS := P.adjacentReverse_source_square_heq ν i j s c L hR hs Z
  have hU := P.adjacentReverse_comparison_heq ν i j s c L hR hs₀ hs Z hij
  exact comp_common_grid_heq hQ hV rfl hS hU

omit hs₀ in
/-- Identify the move/target-square route on the common grid. -/
theorem adjacentReverse_square_right_heq (hij : i ≠ j) :
    HEq ((crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true false true trivial hR trivial hs) (SPath.three false true true hR trivial trivial hs) Z ≫
    crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false true true hR trivial trivial hs) (SPath.three false true true hR trivial trivial rfl) Z) ≫
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial rfl) (SPath.three true false true trivial hR trivial rfl) Z)
      (P.adjacentReverseMove i j s hR hs Z ≫
      (-(c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
        c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
        (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).inv))) := by
  have hQ := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false true trivial hR trivial hs Z
  have hV := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  have hM := P.adjacentReverse_move_heq ν i j s c L hR hs Z hij
  have hT := P.adjacentReverse_target_square_heq ν i j s c L hR Z
  exact comp_common_grid_heq hQ rfl rfl hM hT

/-- The square rectangle after literal crossing-entry identification. -/
theorem adjacentReverse_square_entries (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial hs) (SPath.three true true false trivial trivial hR hs) Z ≫
    (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true true false trivial trivial hR hs) (SPath.three true true false trivial trivial hR rfl) Z ≫
    crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three true true false trivial trivial hR rfl) (SPath.three true false true trivial hR trivial rfl) Z) =
    (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true false true trivial hR trivial hs) (SPath.three false true true hR trivial trivial hs) Z ≫
    crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false true true hR trivial trivial hs) (SPath.three false true true hR trivial trivial rfl) Z) ≫
    crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial rfl) (SPath.three true false true trivial hR trivial rfl) Z := by
  have hleft := P.adjacentReverse_square_left_heq ν i j s hR c L hs₀ hs Z hij
  have hright := P.adjacentReverse_square_right_heq ν i j s hR c L hs Z hij
  have hraw := heq_of_eq (P.adjacentReverse_square_rectangle i j s hR hs₀ hs Z c hc h hij)
  exact eq_of_heq (hleft.trans (hraw.trans hright.symm))

/-- The literal reverse split square entry. -/
theorem adjacentReverse_braid_square (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three true false true trivial hR trivial rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three true false true trivial hR trivial hs) (SPath.three true false true trivial hR trivial rfl) Z := by
  rw [P.adjacentReverse_left_q (P.swappedGens c L) ν i j s hR hs Z hij,
    P.adjacentReverse_right_b (P.swappedGens c L) ν i j s hR hs Z hij]
  symm
  rw [Category.assoc]
  exact P.adjacentReverse_square_entries ν i j s hR c L hs₀ hs Z hc h hij

/-- The literal reverse split conj entry. -/
theorem adjacentReverse_braid_conj (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) j i i ν
      (SPath.three true true false trivial trivial hR hs) (SPath.three true false true trivial hR trivial rfl) Z =
    braidRight (P.swappedGens c L) j i i ν
      (SPath.three true true false trivial trivial hR hs) (SPath.three true false true trivial hR trivial rfl) Z := by
  rw [P.adjacentReverse_left_v (P.swappedGens c L) ν i j s hR hs Z hij,
    P.adjacentReverse_right_b (P.swappedGens c L) ν i j s hR hs Z hij]
  symm
  rw [Category.assoc]
  have hQ := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true false true trivial hR trivial hs Z
  have hV := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  apply rectangle_of_heq hV hV hV rfl rfl
    (P.adjacentReverse_source_conj_heq ν i j s c L hR hs Z)
    (P.adjacentReverse_comparison_heq ν i j s c L hR hs₀ hs Z hij)
    (P.adjacentReverse_comparison_heq ν i j s c L hR hs₀ hs Z hij)
    (P.adjacentReverse_target_conj_heq ν i j s c L hR Z)
  apply heq_of_eq
  have hr := (P.adjacentReverse_splitMatrix i j s hR hs₀ hs Z c hc h hij).2.2.2
  simpa only [Functor.map_neg, Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc] using hr

end CommonGrid

/-- The literal `j i i → i i j` braid for arbitrary paths at the occupied
split endpoint, with one repeated-colour reservoir and two probes. -/
theorem adjacentReverse_braid (ν : X) (i j : I) (s : Sector I)
    (hR : StepValid (true, i) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (p : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))
    (q : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))
    (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    braidLeft (P.swappedGens c L) j i i ν p q Z =
      braidRight (P.swappedGens c L) j i i ν p q Z := by
  have hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
      nextSector (true, j) true (nextSector (true, i) true s) := by
    simp only [nextSector, add_right_comm]
  have hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
      nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) := by
    simp only [nextSector, add_right_comm]
  rcases adjacentMixed_jii_cases hij hR hs hs p with rfl | rfl <;>
    rcases adjacentMixed_iij_cases hij hR rfl rfl q with rfl | rfl
  · exact P.adjacentReverse_braid_diag ν i j s hR c L hs₀ hs Z hc h hij
  · exact P.adjacentReverse_braid_square ν i j s hR c L hs₀ hs Z hc h hij
  · exact P.adjacentReverse_braid_J ν i j s hR c L hs₀ hs Z hc h hij
  · exact P.adjacentReverse_braid_conj ν i j s hR c L hs₀ hs Z hc h hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseRectangle
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseReduction

/-! # Reverse adjacent split matrix entries

Literal path entries for the reverse adjacent components of Brundan–Ellis (1.9).
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
variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))


/-- The source diag entry in the common grid. -/
theorem adjacentReverse_source_diag_heq :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z)
      ((P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact heq_of_eq (P.adjacentMixed_target_diag ν i j s hR c L Z)

/-- The source J entry in the common grid. -/
theorem adjacentReverse_source_J_heq :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true false true trivial hR trivial hs) Z)
      ((P.step (true, j) true s trivial).map
        (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).hom) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact heq_of_eq (P.adjacentSplit_target_J ν i j s hR c L Z)

/-- The source square entry in the common grid. -/
theorem adjacentReverse_source_square_heq :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three true true false trivial trivial hR hs) Z)
      ((P.step (true, j) true s trivial).map
        (-(c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
          c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
          (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv))) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact heq_of_eq (P.adjacentSplit_target_square ν i j s hR c L Z)

/-- The source conj entry in the common grid. -/
theorem adjacentReverse_source_conj_heq :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR hs) Z)
      ((P.step (true, j) true s trivial).map
        (-((P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).hom ≫
          c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
          (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv))) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact heq_of_eq (P.adjacentSplit_target_conj ν i j s hR c L Z)

/-- The target diag entry in the common grid. -/
theorem adjacentReverse_target_diag_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial rfl)
      (SPath.three false true true hR trivial trivial rfl) Z)
      (c.a i s hR ((P.step (true, j) true _ trivial).obj Z)) := by
  exact P.adjacentMixed_source_diag_heq ν i j s hR c L rfl Z

/-- The target J entry in the common grid. -/
theorem adjacentReverse_target_J_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false true trivial hR trivial rfl)
      (SPath.three false true true hR trivial trivial rfl) Z)
      ((P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).hom) := by
  exact P.adjacentSplit_source_J_heq ν i j s hR c L rfl Z

/-- The target square entry in the common grid. -/
theorem adjacentReverse_target_square_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial rfl)
      (SPath.three true false true trivial hR trivial rfl) Z)
      (-(c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
        c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
        (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).inv)) := by
  exact P.adjacentSplit_source_square_heq ν i j s hR c L rfl Z

/-- The target conj entry in the common grid. -/
theorem adjacentReverse_target_conj_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false true trivial hR trivial rfl)
      (SPath.three true false true trivial hR trivial rfl) Z)
      (-((P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).hom ≫
        c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
        (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).inv)) := by
  exact P.adjacentSplit_source_conj_heq ν i j s hR c L rfl Z

/-- The mixed comparison edge from `q` to `m`. -/
theorem adjacentReverse_outer_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three false true true hR trivial trivial hs) Z)
      (P.mixedJ j i s hR
        ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν j i i
    (SPath.two true false trivial hR rfl) (SPath.two false true hR trivial rfl)
    (.cons _ true _ trivial (.nil _)) Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  rfl

/-- The probe edge from `m` to `a`. -/
theorem adjacentReverse_rightProbe_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial rfl) Z)
      ((P.step (true, i) false s hR).map
        (P.preCrossNe j i (nextSector (true, i) false s) hs Z)) := by
  exact P.distinctProbe_right ν j i i s hR hs c L Z hij.symm

/-- The reverse route from `q` through `m` to `a`. -/
theorem adjacentReverse_move_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three false true true hR trivial trivial hs) Z ≫
      crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial rfl) Z)
      (P.adjacentReverseMove i j s hR hs Z) := by
  exact comp_common_grid_heq
    (P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true false true trivial hR trivial hs Z)
    (P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false true true hR trivial trivial hs Z) rfl
    (P.adjacentReverse_outer_heq ν i j s c L hR hs Z hij)
    (P.adjacentReverse_rightProbe_heq ν i j s c L hR hs Z hij)

/-- The mixed comparison edge from `n` to `b`. -/
theorem adjacentReverse_inner (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true false true trivial hR trivial rfl) Z =
      (P.step (true, i) true s trivial).map
        (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν i j i true trivial
    (SPath.two true false trivial hR rfl) (SPath.two false true hR trivial rfl) Z).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  rfl

/-- The outer probe edge from `v` to `n`, including terminal transport. -/
theorem adjacentReverse_probe_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR rfl) Z)
      (P.adjacentReverseProbeCross i j s hR hs₀ Z) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true s)) :=
    SPath.two true true trivial trivial hs₀
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true s)) :=
    SPath.two true true trivial trivial rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, j) true (nextSector (true, i) true s))
      (nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s))) :=
    .cons _ false _ hR (.nil _)
  have hp : SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR hs = pg.append pv := by
    rcases adjacentMixed_jii_cases hij hR hs hs (pg.append pv) with h | h
    · cases h
    · exact h.symm
  have hq : SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR rfl = qg.append pv := rfl
  erw [hp, hq, crossEntry_left]
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  have hc := P.twoTwo_two_heq
      ⟨up j, SKM.wt D (SKM.wt D ν [up i]) [up i]⟩ ⟨up i, SKM.wt D ν [up i]⟩
      ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up j]⟩ ⟨up j, SKM.wt D ν [up i]⟩
      (P.crossNeEntry j i _ _ _ _) (t := s) true true true true
      trivial trivial trivial trivial hs₀ rfl rfl
      ((P.pathFunctor pv).obj Z) ((P.pathFunctor pv).obj Z) HEq.rfl
  refine hc.trans ?_
  change HEq (P.preCrossNe j i s hs₀ ((P.pathFunctor pv).obj Z)) _
  simpa only [adjacentReverseProbeCross, eqToHom_refl, Category.comp_id, castH,
    pv, pathFunctor, Functor.comp_obj, Functor.id_obj] using
    (sandwich_heq (congrArg (fun Y => (P.step (true, j) true s trivial).obj
      ((P.step (true, i) true _ trivial).obj Y))
      (P.reservoirDot_cast i hs₀ hR hR Z).1).symm rfl
      (P.preCrossNe j i s hs₀ ((P.pathFunctor pv).obj Z))).symm

/-- The reverse route from `v` through `n` to `b`. -/
theorem adjacentReverse_comparison_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR rfl) Z ≫
      crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true false true trivial hR trivial rfl) Z)
      (P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
        (P.step (true, i) true s trivial).map
          (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom) := by
  exact comp_common_grid_heq
    (P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR hs Z) rfl rfl
    (P.adjacentReverse_probe_heq ν i j s c L hR hs₀ hs Z hij)
    (heq_of_eq (P.adjacentReverse_inner ν i j s c L hR Z hij))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedRectangle

/-! # Adjacent mixed braid matrix

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

section Edges
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  {t : Sector I}
  (e : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) = t)
  (Z : P.H t)

/-- The source off-diagonal comparison entry. -/
theorem adjacentSplit_source_J_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false true trivial hR trivial e)
      (SPath.three false true true hR trivial trivial e) Z)
      ((P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).hom) := by
  subst e
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two true false trivial hR rfl) (SPath.two false true hR trivial rfl)
    (.cons _ true _ trivial (.nil _)) Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

/-- The source square-coefficient entry. -/
theorem adjacentSplit_source_square_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial e)
      (SPath.three true false true trivial hR trivial e) Z)
      (-(c.a i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z)) ≫
        c.a i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z)) ≫
        (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).inv)) := by
  subst e
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two false true hR trivial rfl) (SPath.two true false trivial hR rfl)
    (.cons _ true _ trivial (.nil _)) Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

/-- The source conjugate-coefficient entry. -/
theorem adjacentSplit_source_conj_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three true false true trivial hR trivial e)
      (SPath.three true false true trivial hR trivial e) Z)
      (-((P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).hom ≫
        c.a i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z)) ≫
        (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).inv)) := by
  subst e
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two true false trivial hR rfl) (SPath.two true false trivial hR rfl)
    (.cons _ true _ trivial (.nil _)) Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  erw [swappedGens_cross_self]
  rfl

end Edges

section Grid
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (hs₀ : nextSector (true, j) true (nextSector (true, i) true s) =
    nextSector (true, i) true (nextSector (true, j) true s))
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

/-- The target comparison entry with the probe spectator. -/
theorem adjacentSplit_target_J :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true false true trivial hR trivial rfl) Z =
      (P.step (true, j) true s trivial).map
        (P.mixedJ i i (nextSector (true, j) true s) hR Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i true trivial
    (SPath.two true false trivial hR rfl) (SPath.two false true hR trivial rfl) Z).trans ?_
  erw [swappedGens_cross_self]
  rfl

/-- The target square-coefficient entry. -/
theorem adjacentSplit_target_square :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      (P.step (true, j) true s trivial).map
        (-(c.a i (nextSector (true, j) true s) hR Z ≫
          c.a i (nextSector (true, j) true s) hR Z ≫
          (P.mixedJ i i (nextSector (true, j) true s) hR Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i true trivial
    (SPath.two false true hR trivial rfl) (SPath.two true false trivial hR rfl) Z).trans ?_
  erw [swappedGens_cross_self]
  rfl

/-- The target conjugate-coefficient entry. -/
theorem adjacentSplit_target_conj :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      (P.step (true, j) true s trivial).map
        (-((P.mixedJ i i (nextSector (true, j) true s) hR Z).hom ≫
          c.a i (nextSector (true, j) true s) hR Z ≫
          (P.mixedJ i i (nextSector (true, j) true s) hR Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i true trivial
    (SPath.two true false trivial hR rfl) (SPath.two true false trivial hR rfl) Z).trans ?_
  erw [swappedGens_cross_self]
  rfl

/-- The inner mixed crossing retains its Q weight. -/
theorem adjacentSplit_inner_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three true true false trivial trivial hR hs) Z)
      ((P.step (true, i) true s trivial).map
        ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
          P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z))) := by
  generalize ht : nextSector (true, i) true (nextSector (true, j) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  refine (heq_of_eq (crossEntry_right (P.swappedGens c L) ν i i j true trivial
    (SPath.two false true hR trivial rfl) (SPath.two true false trivial hR rfl) Z)).trans ?_
  apply heq_of_eq
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  rfl

/-- The outer probe crossing, with repeated reservoir colour permitted. -/
theorem adjacentSplit_probe_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR rfl) Z)
      (P.adjacentMixedProbeCross i j s hR hs₀ Z) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial hs₀
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, i) true (nextSector (true, j) true s))
      (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s))) :=
    .cons _ false _ hR (.nil _)
  have hp : SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR hs = pg.append pv := by
    rcases adjacentMixed_iji_cases hij hR rfl hs (pg.append pv) with h | h
    · cases h
    · exact h.symm
  have hq : SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR rfl = qg.append pv := rfl
  erw [hp, hq, crossEntry_left]
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  have hc := P.twoTwo_two_heq
      ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up j]⟩ ⟨up j, SKM.wt D ν [up i]⟩
      ⟨up j, SKM.wt D (SKM.wt D ν [up i]) [up i]⟩ ⟨up i, SKM.wt D ν [up i]⟩
      (P.crossNeEntry i j _ _ _ _) (t := s) true true true true
      trivial trivial trivial trivial hs₀ rfl rfl
      ((P.pathFunctor pv).obj Z) ((P.pathFunctor pv).obj Z) HEq.rfl
  refine hc.trans ?_
  change HEq (P.preCrossNe i j s hs₀ ((P.pathFunctor pv).obj Z)) _
  simpa only [adjacentMixedProbeCross, eqToHom_refl, Category.comp_id, castH,
    pv, pathFunctor, Functor.comp_obj, Functor.id_obj] using
    (sandwich_heq (congrArg (fun Y => (P.step (true, i) true s trivial).obj
      ((P.step (true, j) true _ trivial).obj Y))
      (P.reservoirDot_cast i hs₀ hR hR Z).1).symm rfl
      (P.preCrossNe i j s hs₀ ((P.pathFunctor pv).obj Z))).symm

/-- The second surviving unequal-crossing route. -/
theorem adjacentSplit_move_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three true true false trivial trivial hR hs) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR rfl) Z)
      ((P.step (true, i) true s trivial).map
        ((P.mixedJ j i (nextSector (true, i) true s) hR (hs ▸ Z)).inv ≫
          P.mixedQ j i (nextSector (true, i) true s) hR (hs ▸ Z)) ≫
        P.adjacentMixedProbeCross i j s hR hs₀ Z) := by
  exact comp_common_grid_heq
    (P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
      true false true trivial hR trivial hs Z)
    (P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR hs Z) rfl
    (P.adjacentSplit_inner_heq ν i j s hR c L hs Z hij)
    (P.adjacentSplit_probe_heq ν i j s hR c L hs₀ hs Z hij)

end Grid
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

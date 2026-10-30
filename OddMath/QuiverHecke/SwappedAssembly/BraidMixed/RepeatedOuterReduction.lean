/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseMatrix
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterDiagonal

/-! # Repeated-outer finite braid sums -/
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

private lemma diagonal_route {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ A) (r' : V ⟶ A)
    (hf : f' = 0) (hr : r' = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f ≫ g) ≫ r := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, add_zero]

private lemma diagonal_row {C : Type u} [Category C] [Preadditive C]
    {A B V T : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ T) (r' : V ⟶ T)
    (hf : f' = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' =
      (f ≫ g) ≫ r + (f ≫ j) ≫ r' := by
  rw [hf]
  simp only [Limits.zero_comp, add_zero]

variable (P : ProbeReservoir k B D Sc) (G : P.Generators)
  (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- Spectator vanishing selects the single left diagonal route. -/
theorem repeatedOuter_braidLeft_route (hij : i ≠ j) :
    let m : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let q : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true false true trivial hR trivial hs
    braidLeft G i j i ν m m Z =
      (crossEntry G ν [] i j [up i] m q Z ≫
        crossEntry G ν [up j] i i [] q q Z) ≫
          crossEntry G ν [] j i [up i] q m Z := by
  classical
  let m : SPath (wd D ν [up i, up j, up i]) s _ :=
    SPath.three false true true hR trivial trivial hs
  let q : SPath (wd D ν [up j, up i, up i]) s _ :=
    SPath.three true false true trivial hR trivial hs
  change braidLeft G i j i ν m m Z =
    (crossEntry G ν [] i j [up i] m q Z ≫ crossEntry G ν [up j] i i [] q q Z) ≫
      crossEntry G ν [] j i [up i] q m Z
  have hfirst := P.crossEntry_left_three_zero G ν i j i false true true true true false
    (by decide) hR trivial trivial trivial trivial hR hs hs Z
  have hlast := P.crossEntry_left_three_zero G ν j i i true true false true false true
    Bool.false_ne_true trivial trivial hR trivial hR trivial hs hs Z
  unfold braidLeft
  rw [adjacentMixed_jii_sum hij hR hs hs]
  simp only [adjacentMixed_jii_sum hij hR hs hs]
  exact diagonal_route _ _ _ _ _ _ _ _ hfirst hlast

/-- Spectator vanishing selects the single right diagonal route. -/
theorem repeatedOuter_braidRight_route (hij : i ≠ j) :
    let m : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let a : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial rfl
    braidRight G i j i ν m m Z =
      (crossEntry G ν [up i] j i [] m a Z ≫
        crossEntry G ν [] i i [up j] a a Z) ≫
          crossEntry G ν [up i] i j [] a m Z := by
  classical
  let m : SPath (wd D ν [up i, up j, up i]) s _ :=
    SPath.three false true true hR trivial trivial hs
  let a : SPath (wd D ν [up i, up i, up j]) s _ :=
    SPath.three false true true hR trivial trivial rfl
  change braidRight G i j i ν m m Z =
    (crossEntry G ν [up i] j i [] m a Z ≫ crossEntry G ν [] i i [up j] a a Z) ≫
      crossEntry G ν [up i] i j [] a m Z
  have hfirst := crossEntry_right_eq_zero G ν i j i false true Bool.false_ne_true
    hR trivial (SPath.two true true trivial trivial hs)
    (SPath.two false true hR trivial rfl) Z
  have hlast := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hR (SPath.two false true hR trivial rfl)
    (SPath.two true true trivial trivial hs) Z
  unfold braidRight
  rw [adjacentMixed_iij_sum hij hR rfl rfl]
  simp only [adjacentMixed_iij_sum hij hR rfl rfl]
  exact diagonal_route _ _ _ _ _ _ _ _ hfirst hlast

/-- Full left braid row for arbitrary target path in the occupied sector. -/
theorem repeatedOuter_braidLeft_row (hij : i ≠ j)
    (q : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    let m : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let a : SPath (wd D ν [up j, up i, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true false true trivial hR trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true true false trivial trivial hR hs
    braidLeft G i j i ν m q Z =
      (crossEntry G ν [] i j [up i] m a Z ≫ crossEntry G ν [up j] i i [] a a Z) ≫ crossEntry G ν [] j i [up i] a q Z +
      (crossEntry G ν [] i j [up i] m a Z ≫ crossEntry G ν [up j] i i [] a b Z) ≫ crossEntry G ν [] j i [up i] b q Z := by
  classical
  let m : SPath (wd D ν [up i, up j, up i]) s _ :=
    SPath.three false true true hR trivial trivial hs
  let a : SPath (wd D ν [up j, up i, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true false true trivial hR trivial hs
  let b : SPath (wd D ν [up j, up i, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true true false trivial trivial hR hs
  change braidLeft G i j i ν m q Z =
    (crossEntry G ν [] i j [up i] m a Z ≫ crossEntry G ν [up j] i i [] a a Z) ≫ crossEntry G ν [] j i [up i] a q Z +
    (crossEntry G ν [] i j [up i] m a Z ≫ crossEntry G ν [up j] i i [] a b Z) ≫ crossEntry G ν [] j i [up i] b q Z
  have hfirst := P.crossEntry_left_three_zero G ν i j i false true true true true false
    (by decide) hR trivial trivial trivial trivial hR hs hs Z
  unfold braidLeft
  rw [adjacentMixed_jii_sum hij hR hs hs]
  simp only [adjacentMixed_jii_sum hij hR hs hs]
  exact diagonal_row _ _ _ _ _ _ _ _ hfirst

/-- Full right braid row for arbitrary target path in the occupied sector. -/
theorem repeatedOuter_braidRight_row (hij : i ≠ j)
    (q : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    let m : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let a : SPath (wd D ν [up i, up i, up j]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three false true true hR trivial trivial rfl
    let b : SPath (wd D ν [up i, up i, up j]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true false true trivial hR trivial rfl
    braidRight G i j i ν m q Z =
      (crossEntry G ν [up i] j i [] m a Z ≫ crossEntry G ν [] i i [up j] a a Z) ≫ crossEntry G ν [up i] i j [] a q Z +
      (crossEntry G ν [up i] j i [] m a Z ≫ crossEntry G ν [] i i [up j] a b Z) ≫ crossEntry G ν [up i] i j [] b q Z := by
  classical
  let m : SPath (wd D ν [up i, up j, up i]) s _ :=
    SPath.three false true true hR trivial trivial hs
  let a : SPath (wd D ν [up i, up i, up j]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three false true true hR trivial trivial rfl
  let b : SPath (wd D ν [up i, up i, up j]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true false true trivial hR trivial rfl
  change braidRight G i j i ν m q Z =
    (crossEntry G ν [up i] j i [] m a Z ≫ crossEntry G ν [] i i [up j] a a Z) ≫ crossEntry G ν [up i] i j [] a q Z +
    (crossEntry G ν [up i] j i [] m a Z ≫ crossEntry G ν [] i i [up j] a b Z) ≫ crossEntry G ν [up i] i j [] b q Z
  have hfirst := crossEntry_right_eq_zero G ν i j i false true Bool.false_ne_true
    hR trivial (SPath.two true true trivial trivial hs)
    (SPath.two false true hR trivial rfl) Z
  unfold braidRight
  rw [adjacentMixed_iij_sum hij hR rfl rfl]
  simp only [adjacentMixed_iij_sum hij hR rfl rfl]
  exact diagonal_row _ _ _ _ _ _ _ _ hfirst

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

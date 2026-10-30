/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentSplitMatrix

/-! # Adjacent mixed braid matrix reductions

The component `Rᵢ Pᵢ Pⱼ → Pⱼ Rᵢ Pᵢ` of Brundan–Ellis (1.9).
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
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

/-- The left braid sum has only its diagonal route at this endpoint. -/
theorem adjacentSplit_left_q (hij : i ≠ j)
    (p : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))) :
    braidLeft (P.swappedGens c L) i i j ν
      p
      (SPath.three true false true trivial hR trivial rfl) Z =
      crossEntry (P.swappedGens c L) ν [] i i [up j]
        p
        (SPath.three false true true hR trivial trivial hs) Z ≫
      (crossEntry (P.swappedGens c L) ν [up i] i j []
        (SPath.three false true true hR trivial trivial hs)
        (SPath.three false true true hR trivial trivial rfl) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
        (SPath.three false true true hR trivial trivial rfl)
        (SPath.three true false true trivial hR trivial rfl) Z) := by
  let t := nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial hs
  let b : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial hs
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let G := P.swappedGens c L
  have hbm : crossEntry G ν [up i] i j [] b m Z = 0 :=
    crossEntry_right_eq_zero G ν i i j true false (by decide) trivial hR _ _ Z
  have hnq : crossEntry G ν [] i j [up i] n q Z = 0 :=
    P.crossEntry_left_three_zero G ν i j i true true true false false true
      Bool.false_ne_true trivial trivial trivial hR hR trivial hs rfl Z
  change braidLeft G i i j ν p q Z =
    crossEntry G ν [] i i [up j] p a Z ≫
      (crossEntry G ν [up i] i j [] a m Z ≫ crossEntry G ν [] i j [up i] m q Z)
  rw [P.adjacentMixed_braidLeft_sum G ν i j hij hR hs hs rfl hs p q Z]
  erw [hbm, hnq]
  simp only [Limits.comp_zero, add_zero, Category.assoc]
  rfl

/-- The left braid sum has only its diagonal route at this endpoint. -/
theorem adjacentSplit_left_v (hij : i ≠ j)
    (p : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))) :
    braidLeft (P.swappedGens c L) i i j ν
      p
      (SPath.three true true false trivial trivial hR rfl) Z =
      crossEntry (P.swappedGens c L) ν [] i i [up j]
        p
        (SPath.three true false true trivial hR trivial hs) Z ≫
      (crossEntry (P.swappedGens c L) ν [up i] i j []
        (SPath.three true false true trivial hR trivial hs)
        (SPath.three true true false trivial trivial hR hs) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
        (SPath.three true true false trivial trivial hR hs)
        (SPath.three true true false trivial trivial hR rfl) Z) := by
  let t := nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial hs
  let b : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial hs
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let G := P.swappedGens c L
  have han : crossEntry G ν [up i] i j [] a n Z = 0 :=
    crossEntry_right_eq_zero G ν i i j false true Bool.false_ne_true hR trivial _ _ Z
  have hmq : crossEntry G ν [] i j [up i] m q Z = 0 :=
    P.crossEntry_left_three_zero G ν i j i false true true true true false
      (by decide) hR trivial trivial trivial trivial hR rfl rfl Z
  change braidLeft G i i j ν p q Z =
    crossEntry G ν [] i i [up j] p b Z ≫
      (crossEntry G ν [up i] i j [] b n Z ≫ crossEntry G ν [] i j [up i] n q Z)
  rw [P.adjacentMixed_braidLeft_sum G ν i j hij hR hs hs rfl hs p q Z]
  erw [han, hmq]
  simp only [Limits.comp_zero, zero_add, Category.assoc]
  rfl

/-- The right braid sum has only its diagonal route at this endpoint. -/
theorem adjacentSplit_right_a (hij : i ≠ j)
    (p : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))) :
    braidRight (P.swappedGens c L) i i j ν
        (SPath.three false true true hR trivial trivial hs)
        p Z =
      (crossEntry (P.swappedGens c L) ν [up i] i j []
        (SPath.three false true true hR trivial trivial hs)
        (SPath.three false true true hR trivial trivial rfl) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
        (SPath.three false true true hR trivial trivial rfl)
        (SPath.three true false true trivial hR trivial rfl) Z) ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
        (SPath.three true false true trivial hR trivial rfl)
        p Z := by
  let t := nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial hs
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let v : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let G := P.swappedGens c L
  have han : crossEntry G ν [up i] i j [] a n Z = 0 :=
    crossEntry_right_eq_zero G ν i i j false true Bool.false_ne_true hR trivial _ _ Z
  have hmv : crossEntry G ν [] i j [up i] m v Z = 0 :=
    P.crossEntry_left_three_zero G ν i j i false true true true true false
      (by decide) hR trivial trivial trivial trivial hR rfl rfl Z
  change braidRight G i i j ν a p Z =
    (crossEntry G ν [up i] i j [] a m Z ≫ crossEntry G ν [] i j [up i] m q Z) ≫
      crossEntry G ν [up j] i i [] q p Z
  rw [P.adjacentMixed_braidRight_sum G ν i j hij hR rfl hs rfl rfl a p Z]
  erw [han, hmv]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero]
  rfl

/-- The right braid sum has only its diagonal route at this endpoint. -/
theorem adjacentSplit_right_b (hij : i ≠ j)
    (p : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))) :
    braidRight (P.swappedGens c L) i i j ν
        (SPath.three true false true trivial hR trivial hs)
        p Z =
      (crossEntry (P.swappedGens c L) ν [up i] i j []
        (SPath.three true false true trivial hR trivial hs)
        (SPath.three true true false trivial trivial hR hs) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
        (SPath.three true true false trivial trivial hR hs)
        (SPath.three true true false trivial trivial hR rfl) Z) ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
        (SPath.three true true false trivial trivial hR rfl)
        p Z := by
  let t := nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial hs
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let v : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let G := P.swappedGens c L
  have ham : crossEntry G ν [up i] i j [] a m Z = 0 :=
    crossEntry_right_eq_zero G ν i i j true false (by decide) trivial hR _ _ Z
  have hnq : crossEntry G ν [] i j [up i] n q Z = 0 :=
    P.crossEntry_left_three_zero G ν i j i true true true false false true
      Bool.false_ne_true trivial trivial trivial hR hR trivial hs rfl Z
  change braidRight G i i j ν a p Z =
    (crossEntry G ν [up i] i j [] a n Z ≫ crossEntry G ν [] i j [up i] n v Z) ≫
      crossEntry G ν [up j] i i [] v p Z
  rw [P.adjacentMixed_braidRight_sum G ν i j hij hR rfl hs rfl rfl a p Z]
  erw [ham, hnq]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero, zero_add]
  rfl

end CommonGrid
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

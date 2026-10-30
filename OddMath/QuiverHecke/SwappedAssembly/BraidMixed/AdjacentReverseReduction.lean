/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentSplitReduction

/-! # Reverse adjacent split braid sum reductions

The finite path sums for the reverse adjacent components of Brundan–Ellis (1.9)
reduce to single routes by the spectator zero entries alone.
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
variable (P : ProbeReservoir k B D Sc) (G : P.Generators)
  (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The four summands of the reverse left braid before spectator vanishing. -/
theorem adjacentReverse_braidLeft_sum (hij : i ≠ j)
    (p : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))
    (w : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    let a : SPath (wd D ν [up i, up i, up j]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial rfl
    let b : SPath (wd D ν [up i, up i, up j]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true false true trivial hR trivial rfl
    let m : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let n : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR rfl
    braidLeft G j i i ν p w Z =
      (crossEntry G ν [] j i [up i] p m Z ≫ crossEntry G ν [up i] j i [] m a Z +
        crossEntry G ν [] j i [up i] p n Z ≫ crossEntry G ν [up i] j i [] n a Z) ≫
          crossEntry G ν [] i i [up j] a w Z +
      (crossEntry G ν [] j i [up i] p m Z ≫ crossEntry G ν [up i] j i [] m b Z +
        crossEntry G ν [] j i [up i] p n Z ≫ crossEntry G ν [up i] j i [] n b Z) ≫
          crossEntry G ν [] i i [up j] b w Z := by
  classical
  dsimp only
  unfold braidLeft
  refine (adjacentMixed_iij_sum hij hR rfl rfl _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg (fun f => f ≫ _) (adjacentMixed_iji_sum hij hR hs rfl _)
  · exact congrArg (fun f => f ≫ _) (adjacentMixed_iji_sum hij hR hs rfl _)

/-- The reverse left braid sum reduces to the route through `m` and `a`. -/
theorem adjacentReverse_left_q (hij : i ≠ j)
    (w : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    braidLeft G j i i ν (SPath.three true false true trivial hR trivial hs)
      w Z =
      (crossEntry G ν [] j i [up i]
        (SPath.three true false true trivial hR trivial hs) (SPath.three false true true hR trivial trivial hs) Z ≫
      crossEntry G ν [up i] j i []
        (SPath.three false true true hR trivial trivial hs) (SPath.three false true true hR trivial trivial rfl) Z) ≫
      crossEntry G ν [] i i [up j]
        (SPath.three false true true hR trivial trivial rfl) w Z := by
  classical
  let t := nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let b : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial hs
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial hs
  let v : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  have hqn : crossEntry G ν [] j i [up i] q n Z = 0 :=
    P.crossEntry_left_three_zero G ν j i i true false true true true false
      (by decide) trivial hR trivial trivial trivial hR hs rfl Z
  have hmb : crossEntry G ν [up i] j i [] m b Z = 0 :=
    crossEntry_right_eq_zero G ν i j i false true Bool.false_ne_true hR trivial _ _ Z
  change braidLeft G j i i ν q w Z =
    (crossEntry G ν [] j i [up i] q m Z ≫
      crossEntry G ν [up i] j i [] m a Z) ≫
      crossEntry G ν [] i i [up j] a w Z
  rw [P.adjacentReverse_braidLeft_sum G ν i j s hR hs Z hij]
  erw [hqn, hmb]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero]
  rfl

/-- The reverse left braid sum reduces to the route through `n` and `b`. -/
theorem adjacentReverse_left_v (hij : i ≠ j)
    (w : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    braidLeft G j i i ν (SPath.three true true false trivial trivial hR hs)
      w Z =
      (crossEntry G ν [] j i [up i]
        (SPath.three true true false trivial trivial hR hs) (SPath.three true true false trivial trivial hR rfl) Z ≫
      crossEntry G ν [up i] j i []
        (SPath.three true true false trivial trivial hR rfl) (SPath.three true false true trivial hR trivial rfl) Z) ≫
      crossEntry G ν [] i i [up j]
        (SPath.three true false true trivial hR trivial rfl) w Z := by
  classical
  let t := nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let b : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial hs
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial hs
  let v : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  have hvm : crossEntry G ν [] j i [up i] v m Z = 0 :=
    P.crossEntry_left_three_zero G ν j i i true true false true false true
      Bool.false_ne_true trivial trivial hR trivial hR trivial hs hs Z
  have hna : crossEntry G ν [up i] j i [] n a Z = 0 :=
    crossEntry_right_eq_zero G ν i j i true false (by decide) trivial hR _ _ Z
  change braidLeft G j i i ν v w Z =
    (crossEntry G ν [] j i [up i] v n Z ≫
      crossEntry G ν [up i] j i [] n b Z) ≫
      crossEntry G ν [] i i [up j] b w Z
  rw [P.adjacentReverse_braidLeft_sum G ν i j s hR hs Z hij]
  erw [hvm, hna]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero, zero_add]
  rfl

/-- The reverse right braid sum reduces to the route through `q` and `m`. -/
theorem adjacentReverse_right_a (hij : i ≠ j)
    (w : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    braidRight G j i i ν w
      (SPath.three false true true hR trivial trivial rfl) Z =
      (crossEntry G ν [up j] i i []
        w (SPath.three true false true trivial hR trivial hs) Z ≫
      crossEntry G ν [] j i [up i]
        (SPath.three true false true trivial hR trivial hs) (SPath.three false true true hR trivial trivial hs) Z) ≫
      crossEntry G ν [up i] j i []
        (SPath.three false true true hR trivial trivial hs) (SPath.three false true true hR trivial trivial rfl) Z := by
  classical
  let t := nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let b : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial hs
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial hs
  let v : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  have hvm : crossEntry G ν [] j i [up i] v m Z = 0 :=
    P.crossEntry_left_three_zero G ν j i i true true false true false true
      Bool.false_ne_true trivial trivial hR trivial hR trivial hs hs Z
  have hna : crossEntry G ν [up i] j i [] n a Z = 0 :=
    crossEntry_right_eq_zero G ν i j i true false (by decide) trivial hR _ _ Z
  unfold braidRight
  rw [adjacentMixed_iji_sum hij hR hs rfl]
  simp only [adjacentMixed_jii_sum hij hR hs hs]
  erw [hvm, hna]
  simp only [Limits.comp_zero, add_zero]

/-- The reverse right braid sum reduces to the route through `v` and `n`. -/
theorem adjacentReverse_right_b (hij : i ≠ j)
    (w : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    braidRight G j i i ν w
      (SPath.three true false true trivial hR trivial rfl) Z =
      (crossEntry G ν [up j] i i []
        w (SPath.three true true false trivial trivial hR hs) Z ≫
      crossEntry G ν [] j i [up i]
        (SPath.three true true false trivial trivial hR hs) (SPath.three true true false trivial trivial hR rfl) Z) ≫
      crossEntry G ν [up i] j i []
        (SPath.three true true false trivial trivial hR rfl) (SPath.three true false true trivial hR trivial rfl) Z := by
  classical
  let t := nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))
  let a : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three false true true hR trivial trivial rfl
  let b : SPath (wd D ν [up i, up i, up j]) s t :=
    SPath.three true false true trivial hR trivial rfl
  let m : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three false true true hR trivial trivial hs
  let n : SPath (wd D ν [up i, up j, up i]) s t :=
    SPath.three true true false trivial trivial hR rfl
  let q : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true false true trivial hR trivial hs
  let v : SPath (wd D ν [up j, up i, up i]) s t :=
    SPath.three true true false trivial trivial hR hs
  have hqn : crossEntry G ν [] j i [up i] q n Z = 0 :=
    P.crossEntry_left_three_zero G ν j i i true false true true true false
      (by decide) trivial hR trivial trivial trivial hR hs rfl Z
  have hmb : crossEntry G ν [up i] j i [] m b Z = 0 :=
    crossEntry_right_eq_zero G ν i j i false true Bool.false_ne_true hR trivial _ _ Z
  unfold braidRight
  rw [adjacentMixed_iji_sum hij hR hs rfl]
  simp only [adjacentMixed_jii_sum hij hR hs hs]
  erw [hqn, hmb]
  simp only [Limits.comp_zero, zero_add]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

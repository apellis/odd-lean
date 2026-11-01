/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReduction

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
private theorem repeatedOuter_polynomial_heq
    {C : Type u} [Category C] [Preadditive C] [Linear k C]
    (i j : I) {A A' : C} (e : A = A')
    {x y z : End A} {x' y' z' : End A'}
    (hx : HEq x x') (hy : HEq y y') (hz : HEq z z') :
    HEq ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow z a ≫ compPow x (D.dn i j - 1 - a))) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • (compPow z a ≫ compPow y d ≫ compPow x (b - 1 - a))) ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (x' ^ (D.dn i j - 1 - a) * z' ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • (x' ^ (b - 1 - a) * y' ^ d * z' ^ a)) := by
  subst e
  cases hx; cases hy; cases hz
  apply heq_of_eq
  simp only [compPow_eq_pow, End.mul_def]

private theorem repeatedOuter_sub_heq
    {C : Type u} [Category C] [Preadditive C]
    {A A' : C} (e : A = A') {l r : End A} {l' r' : End A'}
    (hl : HEq l l') (hr : HEq r r') : HEq (l - r) (l' - r') := by
  subst e
  cases hl; cases hr; rfl

variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The Q-weighted outer edge, with its endpoint transport. -/
theorem repeatedOuter_outer_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z)
      ((P.mixedJ j i s hR
        ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
       P.mixedQ j i s hR
        ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact heq_of_eq (P.adjacentMixed_mixed ν i j s hR c L Z hij)

/-- The return probe crossing is the actual opposite crossing, not an inverse. -/
theorem repeatedOuter_back_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three false true true hR trivial trivial rfl)
      (SPath.three false true true hR trivial trivial hs) Z)
      (P.repeatedOuterProbeBack i j s hR hs Z) := by
  refine (heq_of_eq (crossEntry_right (P.swappedGens c L) ν i i j false hR
    (SPath.two true true trivial trivial rfl)
    (SPath.two true true trivial trivial hs) Z)).trans ?_
  apply map_of_heq _ rfl (P.pathFunctor_two_obj
    (c₁ := ⟨up j, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
    true true trivial trivial hs Z _ (P.castH_obj_heq hs Z))
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  have he := P.twoTwo_two_heq
    ⟨up i, SKM.wt D ν [up j]⟩ ⟨up j, ν⟩
    ⟨up j, SKM.wt D ν [up i]⟩ ⟨up i, ν⟩
    (P.crossNeEntry i j _ _ _ _) (t := nextSector (true, i) false s)
    true true true true trivial trivial trivial trivial rfl hs rfl Z
    ((P.castH hs).obj Z) (P.castH_obj_heq hs Z)
  exact he.trans (eqToHom_comp_heq _ _).symm

/-- Reassociate the raw left route without changing any edge. -/
private theorem repeatedOuter_left_assoc :
    let J := P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
    let Q := P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
    let A := (P.step (true, j) true s trivial).map
      (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
    ((J.inv ≫ Q) ≫ A) ≫ J.hom = P.repeatedOuterDiagonalLeft i j s hR hs Z c := by
  dsimp only
  rw [Category.assoc, Category.assoc]
  rfl

omit hs Z in
/-- The returning mixed edge on an arbitrary transported endpoint. -/
theorem repeatedOuter_return_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t)
    (Z : P.H t) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three false true true hR trivial trivial hs) Z)
      (P.mixedJ j i s hR
        ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom := by
  subst hs
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν j i i
    (SPath.two true false trivial hR rfl) (SPath.two false true hR trivial rfl)
    (.cons _ true _ trivial (.nil _)) Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij.symm]
  rfl

omit hs Z in
/-- The first two edges identify with the raw Q-weighted route. -/
theorem repeatedOuter_left_pair_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t)
    (Z : P.H t) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
        (SPath.three true false true trivial hR trivial hs)
        (SPath.three true false true trivial hR trivial hs) Z)
      (((P.mixedJ j i s hR
          ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
        P.mixedQ j i s hR
          ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))) ≫
        (P.step (true, j) true s trivial).map
          (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))) := by
  subst hs
  exact comp_common_grid_heq rfl rfl rfl
    (heq_of_eq (P.adjacentMixed_mixed ν i j s hR c L Z hij))
    (heq_of_eq (P.adjacentMixed_target_diag ν i j s hR c L Z))

/-- The entire left finite sum identifies with the raw Q-weighted route. -/
theorem repeatedOuter_left_entries_heq (hij : i ≠ j) :
    HEq ((crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
        (SPath.three true false true trivial hR trivial hs)
        (SPath.three true false true trivial hR trivial hs) Z) ≫
      crossEntry (P.swappedGens c L) ν [] j i [up i]
        (SPath.three true false true trivial hR trivial hs)
        (SPath.three false true true hR trivial trivial hs) Z)
      ((((P.mixedJ j i s hR
          ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
        P.mixedQ j i s hR
          ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))) ≫
        (P.step (true, j) true s trivial).map
          (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))) ≫
        (P.mixedJ j i s hR
          ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact comp_common_grid_heq rfl rfl rfl
    (P.repeatedOuter_left_pair_heq ν i j s c L hR rfl Z hij)
    (P.repeatedOuter_return_heq ν i j s c L hR rfl Z hij)

/-- Identification of the full left finite path sum. -/
theorem repeatedOuter_left_heq (hij : i ≠ j) :
    HEq (braidLeft (P.swappedGens c L) i j i ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial hs) Z)
      (P.repeatedOuterDiagonalLeft i j s hR hs Z c) := by
  exact (heq_of_eq (P.repeatedOuter_braidLeft_route (P.swappedGens c L)
    ν i j s hR hs Z hij)).trans
    ((P.repeatedOuter_left_entries_heq ν i j s c L hR hs Z hij).trans
      (heq_of_eq (P.repeatedOuter_left_assoc i j s c hR hs Z)))

/-- The entire right finite sum identifies with the two actual probe crossings. -/
theorem repeatedOuter_right_heq (hij : i ≠ j) :
    HEq (braidRight (P.swappedGens c L) i j i ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial hs) Z)
      (P.repeatedOuterDiagonalRight i j s hR hs Z c) := by
  rw [P.repeatedOuter_braidRight_route (P.swappedGens c L) ν i j s hR hs Z hij]
  have hm := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false true true hR trivial trivial hs Z
  have he := comp_common_grid_heq hm rfl hm
    (comp_common_grid_heq hm rfl rfl
      (P.adjacentReverse_rightProbe_heq ν i j s c L hR hs Z hij)
      (P.adjacentReverse_target_diag_heq ν i j s c L hR Z))
    (P.repeatedOuter_back_heq ν i j s c L hR hs Z hij)
  exact he.trans (heq_of_eq (Category.assoc _ _ _))

omit hs Z in
/-- The literal X dot at an arbitrary transported endpoint. -/
theorem repeatedOuter_dotX_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (SPath.three false true true hR trivial trivial hs) Z)
      (P.dotDiag i false s hR ((P.step (true, j) true _ trivial).obj ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ false _ hR (.nil _)) (.cons _ false _ hR (.nil _)) (SPath.two true true trivial trivial rfl) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_reservoir i (SKM.wt D ν [up j, up i]) s hR hR _)

omit hs Z in
/-- The literal Y dot at an arbitrary transported endpoint. -/
theorem repeatedOuter_dotY_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (SPath.three false true true hR trivial trivial hs) Z)
      ((P.step (true, i) false s hR).map (P.dotDiag j true _ trivial ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ false s hR (.nil _))
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) false s hR).map
    (P.dotImage_probe j (SKM.wt D ν [up i]) (nextSector (true, i) false s) trivial trivial
      ((P.step (true, i) true _ trivial).obj Z)))

omit hs Z in
/-- The literal Z dot at an arbitrary transported endpoint. -/
theorem repeatedOuter_dotZ_heq {t : Sector I}
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t)
    (Z : P.H t) :
    HEq (dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (SPath.three false true true hR trivial trivial hs) Z)
      ((P.step (true, i) false s hR).map ((P.step (true, j) true _ trivial).map (P.dotDiag i true _ trivial ((P.castH hs).obj Z)))) := by
  subst hs
  unfold dotEntry
  refine (heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two false true hR trivial rfl)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _)) (.nil _) _ _ rfl rfl Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) false s hR).map
    ((P.step (true, j) true _ trivial).map f))
    (P.dotImage_probe i ν (nextSector (true, j) true (nextSector (true, i) false s))
      trivial trivial Z))

/-- The full braid difference, on the raw common object grid. -/
theorem repeatedOuter_difference_heq (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    let p : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three false true true hR trivial trivial hs
    HEq (braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z) ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        ((P.repeatedOuterX i j s hR hs Z) ^ (D.dn i j - 1 - a) * (P.repeatedOuterZ i j s hR hs Z) ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • ((P.repeatedOuterX i j s hR hs Z) ^ (b - 1 - a) * (P.repeatedOuterY i j s hR hs Z) ^ d * (P.repeatedOuterZ i j s hR hs Z) ^ a)) := by
  exact (repeatedOuter_sub_heq (P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false true true hR trivial trivial hs Z)
    (P.repeatedOuter_left_heq ν i j s c L hR hs Z hij)
    (P.repeatedOuter_right_heq ν i j s c L hR hs Z hij)).trans
      (heq_of_eq (P.repeatedOuterDiagonal_correction i j s hR hs Z c hc h hij))

/-- The full literal dot correction, on the raw common object grid. -/
theorem repeatedOuter_correction_heq :
    let p : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three false true true hR trivial trivial hs
    HEq ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫ compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (D.dn i j - 1 - a))) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫ compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫ compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a))) ((∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        ((P.repeatedOuterX i j s hR hs Z) ^ (D.dn i j - 1 - a) * (P.repeatedOuterZ i j s hR hs Z) ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • ((P.repeatedOuterX i j s hR hs Z) ^ (b - 1 - a) * (P.repeatedOuterY i j s hR hs Z) ^ d * (P.repeatedOuterZ i j s hR hs Z) ^ a)) := by
  exact repeatedOuter_polynomial_heq i j (P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false true true hR trivial trivial hs Z)
    (P.repeatedOuter_dotX_heq ν i j s c L hR hs Z)
    (P.repeatedOuter_dotY_heq ν i j s c L hR hs Z)
    (P.repeatedOuter_dotZ_heq ν i j s c L hR hs Z)

/-- The literal `CrossBraid.braidEq_diag` correction for `Rᵢ Pⱼ Pᵢ`.
Both parity cases and all coefficient terms are retained. -/
theorem repeatedOuter_braidEq_diag (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    let p : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three false true true hR trivial trivial hs
    braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z = (∑ a ∈ Finset.range (D.dn i j), (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫ compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (D.dn i j - 1 - a))) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) • (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫ compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫ compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a)) := by
  exact eq_of_heq ((P.repeatedOuter_difference_heq ν i j s c L hR hs Z hc h hij).trans
    (P.repeatedOuter_correction_heq ν i j s c L hR hs Z).symm)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

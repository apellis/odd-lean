/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedCoefficient

/-! # Adjacent mixed braid component

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

/-- Terminal transport for a three-step path object. -/
theorem pathFunctor_three_obj {c₁ c₂ c₃ : Col I X} {s t : Sector I}
    (a b c : Bool) (ha : StepValid c₁.l a s)
    (hb : StepValid c₂.l b (nextSector c₁.l a s))
    (hc : StepValid c₃.l c (nextSector c₂.l b (nextSector c₁.l a s)))
    (e : nextSector c₃.l c (nextSector c₂.l b (nextSector c₁.l a s)) = t)
    (Z : P.H t) :
    (P.pathFunctor (SPath.three (c₁ := c₁) (c₂ := c₂) (c₃ := c₃)
      a b c ha hb hc e)).obj Z =
      (P.step c₁.l a s ha).obj ((P.step c₂.l b _ hb).obj
        ((P.step c₃.l c _ hc).obj (e ▸ Z))) := by
  subst e
  rfl

/-- A left crossing cannot change the third summand bit. -/
theorem crossEntry_left_three_zero (gens : P.Generators) (ν : X) (i j r : I)
    {s t : Sector I} (a b d e f g : Bool) (hfg : f ≠ g)
    (ha : StepValid (up i) a s) (hb : StepValid (up j) b (nextSector (up i) a s))
    (hd : StepValid (up j) d s) (he : StepValid (up i) e (nextSector (up j) d s))
    (hf : StepValid (up r) f (nextSector (up j) b (nextSector (up i) a s)))
    (hg : StepValid (up r) g (nextSector (up i) e (nextSector (up j) d s)))
    (ep : nextSector (up r) f (nextSector (up j) b (nextSector (up i) a s)) = t)
    (eq : nextSector (up r) g (nextSector (up i) e (nextSector (up j) d s)) = t)
    (Z : P.H t) :
    crossEntry gens ν [] i j [up r]
      (SPath.three a b f ha hb hf ep) (SPath.three d e g hd he hg eq) Z = 0 := by
  apply crossEntry_left_eq_zero gens ν i j r
    (SPath.two a b ha hb rfl) (SPath.two d e hd he rfl)
    (.cons _ f _ hf (ep ▸ .nil _)) (.cons _ g _ hg (eq ▸ .nil _)) _ Z
  intro h
  exact hfg (congrArg (fun p : Σ z, SPath (wd D ν [up r]) z t =>
    match p.2 with | .cons _ bit _ _ _ => bit) h)

section Edges
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  {t : Sector I}
  (e : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) = t)
  (Z : P.H t)

/-- The diagonal repeated crossing at the source, with its terminal transport. -/
theorem adjacentMixed_source_diag_heq :
    HEq (crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial e)
      (SPath.three false true true hR trivial trivial e) Z)
      (c.a i s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))) := by
  subst e
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i i j
    (SPath.two false true hR trivial rfl) (SPath.two false true hR trivial rfl)
    (.cons _ true _ trivial (.nil _)) Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  rw [swappedGens_cross_self]
  rfl

end Edges

section CommonGrid
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

/-- The diagonal crossing at the target is the spectator image of the coefficient. -/
theorem adjacentMixed_target_diag :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial rfl)
      (SPath.three true false true trivial hR trivial rfl) Z =
    (P.step (true, j) true s trivial).map
      (c.a i (nextSector (true, j) true s) hR Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i true trivial
    (SPath.two false true hR trivial rfl) (SPath.two false true hR trivial rfl) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

/-- The first unequal crossing in the common grid. -/
theorem adjacentMixed_probe_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial rfl) Z)
      ((P.step (true, i) false s hR).map
        (P.preCrossNe i j (nextSector (true, i) false s) hs Z)) := by
  exact P.distinctProbe_right ν i j i s hR hs c L Z hij

/-- The second unequal crossing retains its full Q factor. -/
theorem adjacentMixed_mixed (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial rfl)
      (SPath.three true false true trivial hR trivial rfl) Z =
    (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj Z)).inv ≫
      P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i j i
    (SPath.two false true hR trivial rfl) (SPath.two true false trivial hR rfl)
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hij]
  rfl

/-- Composition respects heterogeneous comparison with a common object grid. -/
theorem comp_common_grid_heq {C : Type*} [Category C] {A B D A' B' D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D')
    {f : A ⟶ B} {g : B ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ D'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst hA hB hD
  cases hf
  cases hg
  rfl

/-- The surviving unequal-crossing product is the coefficient-transport map. -/
theorem adjacentMixed_move_heq (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial rfl) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial rfl)
      (SPath.three true false true trivial hR trivial rfl) Z)
      (P.adjacentMixedMove i j s hR hs Z) := by
  exact comp_common_grid_heq
    (P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
      false true true hR trivial trivial hs Z) rfl rfl
    (P.adjacentMixed_probe_heq ν i j s hR c L hs Z hij)
    (heq_of_eq (P.adjacentMixed_mixed ν i j s hR c L Z hij))

/-- The left braid sum has only its diagonal route at this endpoint. -/
theorem adjacentMixed_braidLeft_reduced (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial rfl) Z =
      crossEntry (P.swappedGens c L) ν [] i i [up j]
        (SPath.three false true true hR trivial trivial hs)
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
  change braidLeft G i i j ν a q Z =
    crossEntry G ν [] i i [up j] a a Z ≫
      (crossEntry G ν [up i] i j [] a m Z ≫ crossEntry G ν [] i j [up i] m q Z)
  rw [P.adjacentMixed_braidLeft_sum G ν i j hij hR hs hs rfl hs a q Z]
  erw [hbm, hnq]
  simp only [Limits.comp_zero, add_zero, Category.assoc]
  rfl

/-- The right braid sum has only its diagonal route at this endpoint. -/
theorem adjacentMixed_braidRight_reduced (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i i j ν
        (SPath.three false true true hR trivial trivial hs)
        (SPath.three true false true trivial hR trivial rfl) Z =
      (crossEntry (P.swappedGens c L) ν [up i] i j []
        (SPath.three false true true hR trivial trivial hs)
        (SPath.three false true true hR trivial trivial rfl) Z ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i]
        (SPath.three false true true hR trivial trivial rfl)
        (SPath.three true false true trivial hR trivial rfl) Z) ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
        (SPath.three true false true trivial hR trivial rfl)
        (SPath.three true false true trivial hR trivial rfl) Z := by
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
  change braidRight G i i j ν a q Z =
    (crossEntry G ν [up i] i j [] a m Z ≫ crossEntry G ν [] i j [up i] m q Z) ≫
      crossEntry G ν [up j] i i [] q q Z
  rw [P.adjacentMixed_braidRight_sum G ν i j hij hR rfl hs rfl rfl a q Z]
  erw [han, hmv]
  simp only [Limits.comp_zero, Limits.zero_comp, add_zero]
  rfl

/-- The literal braid equality on `Rᵢ Pᵢ Pⱼ → Pⱼ Rᵢ Pᵢ`.
Only inverse coefficients and the existing coefficient inputs are required;
no crossing or mixed Q polynomial is assumed invertible. -/
theorem adjacentMixed_braid (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial rfl) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial rfl) Z := by
  rw [P.adjacentMixed_braidLeft_reduced ν i j s hR c L hs Z hij,
    P.adjacentMixed_braidRight_reduced ν i j s hR c L hs Z hij]
  have hA := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
    false true true hR trivial trivial hs Z
  exact rectangle_of_heq hA hA hA rfl rfl
    (P.adjacentMixed_source_diag_heq ν i j s hR c L hs Z)
    (P.adjacentMixed_move_heq ν i j s hR c L hs Z hij)
    (P.adjacentMixed_move_heq ν i j s hR c L hs Z hij)
    (heq_of_eq (P.adjacentMixed_target_diag ν i j s hR c L Z))
    (heq_of_eq (P.adjacentMixedMove_coeff c hc h i j s hR hs Z hij))

end CommonGrid
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Quad

/-! # The dot slide relations in the swapped layer representation

The relations `slideL`, `slideLEq`, `slideR` and `slideREq` of `OddMath.SKM.Presentation` are
(1.8) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5:
a dot slides through the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` up to the sign
`(-1)^{|i||j|}`, with the correction term `1` for `i = j`.

In the swapped layer representation each relation is one matrix identity per pair of
summand paths `p` of `Eᵢ Eⱼ`, `q` of `Eⱼ Eᵢ` and object `Z`. Since the dot entries are
diagonal, the entry of a dot followed by a crossing is the dot entry at `p` composed with the
crossing entry (`compDiag_leftDot_cross`, `compDiag_rightDot_cross`), and the entry of a crossing
followed by a dot is the crossing entry composed with the dot entry at `q`
(`compDiag_cross_rightDot`, `compDiag_cross_leftDot`).

`CrossSlide gens` states the four matrix identities; `slideRelations` derives
`SlideRelations` from it.

Main declarations: `ProbeReservoir.compDiag_crossL`, `ProbeReservoir.CrossSlide`,
`ProbeReservoir.slideRelations`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- The single crossing layer `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` is a chain. -/
theorem sChain_crossL (i j : I) :
    SKM.SChain [up i, up j] (SKM.crossL [] i j []) [up j, up i] := by
  simp [SKM.crossL, SKM.Shape.dom, SKM.Shape.cod]

/-- The entry of the crossing diagram `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` is the crossing image. -/
theorem compDiag_crossL (gens : P.Generators) (i j : I) (ν : X)
    (h : SKM.SChain [up i, up j] (SKM.crossL [] i j []) [up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.crossL [] i j []) h) p q Z = gens.cross i j ν p q Z := by
  show compList gens (a := SKM.ob D ν [up i, up j]) (b := SKM.ob D ν [up j, up i])
    [SKM.lay D ν [] (SKM.Shape.cross i j) []] (h.chain D ν) p q Z = _
  erw [compList_one]
  simp only [SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact compLayer_cross gens i j ν p q Z

open Classical in
/-- The entry of a dot on the left strand followed by `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`. -/
theorem compDiag_leftDot_cross (gens : P.Generators) (i j : I) (ν : X)
    (h : SKM.SChain [up i, up j] (SKM.dotsL [] i [up j] 1 ++ SKM.crossL [] i j [])
      [up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z = leftDot gens i j ν p Z ≫ gens.cross i j ν p q Z := by
  rw [show SKM.mkD D ν _ h = SKM.mkD D ν (SKM.dotsL [] i [up j] 1)
      (SKM.sChain_dotsL [] i [up j] 1) ≫ SKM.mkD D ν (SKM.crossL [] i j []) (sChain_crossL i j)
      from (SKM.mkD_comp D ν _ _ _ _).symm]
  rw [compDiag_comp]
  refine (Finset.sum_eq_single p (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_leftDots gens i j ν 1 p m Z]
    simp [Ne.symm hm]
  · erw [compDiag_leftDots gens i j ν 1 p p Z, compDiag_crossL]
    simp [compPow]

open Classical in
/-- The entry of a dot on the right strand followed by `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`. -/
theorem compDiag_rightDot_cross (gens : P.Generators) (i j : I) (ν : X)
    (h : SKM.SChain [up i, up j] (SKM.dotsL [up i] j [] 1 ++ SKM.crossL [] i j [])
      [up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z = rightDot gens i j ν p Z ≫ gens.cross i j ν p q Z := by
  rw [show SKM.mkD D ν _ h = SKM.mkD D ν (SKM.dotsL [up i] j [] 1)
      (SKM.sChain_dotsL [up i] j [] 1) ≫ SKM.mkD D ν (SKM.crossL [] i j []) (sChain_crossL i j)
      from (SKM.mkD_comp D ν _ _ _ _).symm]
  rw [compDiag_comp]
  refine (Finset.sum_eq_single p (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_rightDots gens i j ν 1 p m Z]
    simp [Ne.symm hm]
  · erw [compDiag_rightDots gens i j ν 1 p p Z, compDiag_crossL]
    simp [compPow]

open Classical in
/-- The entry of `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` followed by a dot on the right strand. -/
theorem compDiag_cross_rightDot (gens : P.Generators) (i j : I) (ν : X)
    (h : SKM.SChain [up i, up j] (SKM.crossL [] i j [] ++ SKM.dotsL [up j] i [] 1)
      [up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z = gens.cross i j ν p q Z ≫ rightDot gens j i ν q Z := by
  rw [show SKM.mkD D ν _ h = SKM.mkD D ν (SKM.crossL [] i j []) (sChain_crossL i j) ≫
      SKM.mkD D ν (SKM.dotsL [up j] i [] 1) (SKM.sChain_dotsL [up j] i [] 1)
      from (SKM.mkD_comp D ν _ _ _ _).symm]
  rw [compDiag_comp]
  refine (Finset.sum_eq_single q (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_rightDots gens j i ν 1 m q Z]
    simp [hm]
  · erw [compDiag_rightDots gens j i ν 1 q q Z, compDiag_crossL]
    simp [compPow]

open Classical in
/-- The entry of `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` followed by a dot on the left strand. -/
theorem compDiag_cross_leftDot (gens : P.Generators) (i j : I) (ν : X)
    (h : SKM.SChain [up i, up j] (SKM.crossL [] i j [] ++ SKM.dotsL [] j [up i] 1)
      [up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z = gens.cross i j ν p q Z ≫ leftDot gens j i ν q Z := by
  rw [show SKM.mkD D ν _ h = SKM.mkD D ν (SKM.crossL [] i j []) (sChain_crossL i j) ≫
      SKM.mkD D ν (SKM.dotsL [] j [up i] 1) (SKM.sChain_dotsL [] j [up i] 1)
      from (SKM.mkD_comp D ν _ _ _ _).symm]
  rw [compDiag_comp]
  refine (Finset.sum_eq_single q (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_leftDots gens j i ν 1 m q Z]
    simp [hm]
  · erw [compDiag_leftDots gens j i ν 1 q q Z, compDiag_crossL]
    simp [compPow]

open Classical in
/-- **The dot slide relations (1.8) for the crossing and dot images**, entry by entry: the
dot entries slide through the crossing entries up to the sign `(-1)^{|i||j|}`
(`zsign k (|i| |j|)`), with the identity as correction term for equal colours. -/
structure CrossSlide (gens : P.Generators) : Prop where
  /-- `(x ⊗ 1) ≫ τ = (-1)^{|i||j|} τ ≫ (1 ⊗ x)` on `Eᵢ Eⱼ`, `i ≠ j`. -/
  slideL : ∀ (i j : I) (ν : X), i ≠ j → ∀ {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t),
    leftDot gens i j ν p Z ≫ gens.cross i j ν p q Z =
      zsign k (D.parity i * D.parity j) • (gens.cross i j ν p q Z ≫ rightDot gens j i ν q Z)
  /-- `(x ⊗ 1) ≫ τ - (-1)^{|i|} τ ≫ (1 ⊗ x) = 1` on `Eᵢ Eᵢ`. -/
  slideLEq : ∀ (i : I) (ν : X) {s t : Sector I} (p q : SPath (wd D ν [up i, up i]) s t)
    (Z : P.H t),
    leftDot gens i i ν p Z ≫ gens.cross i i ν p q Z -
        zsign k (D.parity i * D.parity i) • (gens.cross i i ν p q Z ≫ rightDot gens i i ν q Z) =
      if hpq : p = q then eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0
  /-- `τ ≫ (x ⊗ 1) = (-1)^{|i||j|} (1 ⊗ x) ≫ τ` on `Eᵢ Eⱼ`, `i ≠ j`. -/
  slideR : ∀ (i j : I) (ν : X), i ≠ j → ∀ {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t),
    gens.cross i j ν p q Z ≫ leftDot gens j i ν q Z =
      zsign k (D.parity i * D.parity j) • (rightDot gens i j ν p Z ≫ gens.cross i j ν p q Z)
  /-- `τ ≫ (x ⊗ 1) - (-1)^{|i|} (1 ⊗ x) ≫ τ = 1` on `Eᵢ Eᵢ`. -/
  slideREq : ∀ (i : I) (ν : X) {s t : Sector I} (p q : SPath (wd D ν [up i, up i]) s t)
    (Z : P.H t),
    gens.cross i i ν p q Z ≫ leftDot gens i i ν q Z -
        zsign k (D.parity i * D.parity i) • (rightDot gens i i ν p Z ≫ gens.cross i i ν p q Z) =
      if hpq : p = q then eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0

variable {Gs Ys : ∀ s, P.H s}

/-- **`SlideRelations` for the swapped layer representation**: the dot slide relations (1.8)
hold, whiskered arbitrarily, as soon as the crossing and dot images satisfy `CrossSlide`. -/
theorem slideRelations {gens : P.Generators} (hs : CrossSlide gens) :
    SlideRelations Sc (P.layerRep Gs Ys gens) := by
  classical
  intro r hr
  cases r with
  | slideL i j ν hij =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up j]) (b := SKM.ob D ν [up j, up i])
      (SKM.relation D Sc (.slideL i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_smul, compEval_of, compEval_of]
    erw [compDiag_leftDot_cross gens i j ν _ p q Z, compDiag_cross_rightDot gens i j ν _ p q Z]
    rw [hs.slideL i j ν hij p q Z]
    exact sub_self _
  | slideLEq i ν =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up i]) (b := SKM.ob D ν [up i, up i])
      (SKM.relation D Sc (.slideLEq i ν)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_sub, compEval_smul, compEval_of, compEval_of, compEval_of]
    erw [compDiag_leftDot_cross gens i i ν _ p q Z, compDiag_cross_rightDot gens i i ν _ p q Z,
      compDiag_id gens p q Z]
    rw [hs.slideLEq i ν p q Z]
    exact sub_self _
  | slideR i j ν hij =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up j]) (b := SKM.ob D ν [up j, up i])
      (SKM.relation D Sc (.slideR i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_smul, compEval_of, compEval_of]
    erw [compDiag_cross_leftDot gens i j ν _ p q Z, compDiag_rightDot_cross gens i j ν _ p q Z]
    rw [hs.slideR i j ν hij p q Z]
    exact sub_self _
  | slideREq i ν =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up i]) (b := SKM.ob D ν [up i, up i])
      (SKM.relation D Sc (.slideREq i ν)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_sub, compEval_smul, compEval_of, compEval_of, compEval_of]
    erw [compDiag_cross_leftDot gens i i ν _ p q Z, compDiag_rightDot_cross gens i i ν _ p q Z,
      compDiag_id gens p q Z]
    rw [hs.slideREq i ν p q Z]
    exact sub_self _
  | _ => simp [relGroup] at hr

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly

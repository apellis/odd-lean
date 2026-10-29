/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Slides

/-! # The braid relations in the swapped layer representation

The relations `braid` and `braidEq` of `OddMath.SKM.Presentation` are (1.9) of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5: the two composites of three
upward crossings `Eᵢ Eⱼ Eₖ → Eₖ Eⱼ Eᵢ` agree unless `i = k ≠ j`, and for `i = k ≠ j` they
differ by the divided-difference correction in the dots built from `Q_ij`.

In the swapped layer representation each relation is one matrix identity per pair of
summand paths `p` of `Eᵢ Eⱼ Eₖ`, `q` of `Eₖ Eⱼ Eᵢ` and object `Z`. The entry of three
crossings is the matrix product of the entries of the three crossing layers (`braidLeft`,
`braidRight`); the dot entries of a three-letter word are diagonal, so the correction terms
are diagonal (`compDiag_dots_dots`, `compDiag_dots_dots_dots`).

`CrossBraid gens` states the matrix identities; `braidRelations` derives `BraidRelations`
from it.

Main declarations: `ProbeReservoir.braidLeft`, `ProbeReservoir.braidRight`,
`ProbeReservoir.CrossBraid`, `ProbeReservoir.braidRelations`.
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

/-- A crossing layer with strands on both sides is a chain. -/
theorem sChain_crossL_whisker (u : List (Letter I)) (i j : I) (v : List (Letter I)) :
    SKM.SChain (u ++ [up i, up j] ++ v) (SKM.crossL u i j v) (u ++ [up j, up i] ++ v) := by
  simp [SKM.crossL, SKM.Shape.dom, SKM.Shape.cod]

/-- The entry of a crossing `τ` on two adjacent strands of a word, with strands `u` on the
left and `v` on the right: the entry of the one-layer crossing diagram. -/
def crossEntry (gens : P.Generators) (ν : X) (u : List (Letter I)) (i j : I)
    (v : List (Letter I)) {s t : Sector I}
    (p : SPath (SKM.ob D ν (u ++ [up i, up j] ++ v)).word s t)
    (q : SPath (SKM.ob D ν (u ++ [up j, up i] ++ v)).word s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  compDiag gens (SKM.mkD D ν (SKM.crossL u i j v) (sChain_crossL_whisker u i j v)) p q Z

/-- The entry of a dot on one strand of a word, with strands `u` on the left and `v` on the
right, at a summand path. -/
def dotEntry (gens : P.Generators) (ν : X) (u : List (Letter I)) (i : I)
    (v : List (Letter I)) {s t : Sector I}
    (p : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).dom.word s t)
    (Z : P.H t) : (P.pathFunctor p).obj Z ⟶ (P.pathFunctor p).obj Z :=
  compLayer gens (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z

open Classical in
/-- The entry of the composite `(τ ⊗ 1) ; (1 ⊗ τ) ; (τ ⊗ 1)` of `Eᵢ Eⱼ Eₖ → Eₖ Eⱼ Eᵢ`. -/
def braidLeft (gens : P.Generators) (i j k' : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up k']) s t) (q : SPath (wd D ν [up k', up j, up i]) s t)
    (Z : P.H t) : (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  letI : Fintype (SPath (wd D ν [up j, up i, up k']) s t) := Fintype.ofFinite _
  letI : Fintype (SPath (wd D ν [up j, up k', up i]) s t) := Fintype.ofFinite _
  ∑ m₂ : SPath (wd D ν [up j, up k', up i]) s t,
    (∑ m₁ : SPath (wd D ν [up j, up i, up k']) s t,
      crossEntry gens ν [] i j [up k'] p m₁ Z ≫ crossEntry gens ν [up j] i k' [] m₁ m₂ Z) ≫
      crossEntry gens ν [] j k' [up i] m₂ q Z

open Classical in
/-- The entry of the composite `(1 ⊗ τ) ; (τ ⊗ 1) ; (1 ⊗ τ)` of `Eᵢ Eⱼ Eₖ → Eₖ Eⱼ Eᵢ`. -/
def braidRight (gens : P.Generators) (i j k' : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up k']) s t) (q : SPath (wd D ν [up k', up j, up i]) s t)
    (Z : P.H t) : (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  letI : Fintype (SPath (wd D ν [up i, up k', up j]) s t) := Fintype.ofFinite _
  letI : Fintype (SPath (wd D ν [up k', up i, up j]) s t) := Fintype.ofFinite _
  ∑ m₂ : SPath (wd D ν [up k', up i, up j]) s t,
    (∑ m₁ : SPath (wd D ν [up i, up k', up j]) s t,
      crossEntry gens ν [up i] j k' [] p m₁ Z ≫ crossEntry gens ν [] i k' [up j] m₁ m₂ Z) ≫
      crossEntry gens ν [up k'] i j [] m₂ q Z

open Classical in
/-- The entry of a composite of three diagrams. -/
theorem compDiag_comp_comp (gens : P.Generators) {a b c d : Obj (SKM.sig D)} (e₁ : a ⟶ b)
    (e₂ : b ⟶ c) (e₃ : c ⟶ d) {s t : Sector I} (p : SPath a.word s t) (q : SPath d.word s t)
    (Z : P.H t) :
    letI := Fintype.ofFinite (SPath b.word s t)
    letI := Fintype.ofFinite (SPath c.word s t)
    compDiag gens ((e₁ ≫ e₂) ≫ e₃) p q Z =
      ∑ m₂, (∑ m₁, compDiag gens e₁ p m₁ Z ≫ compDiag gens e₂ m₁ m₂ Z) ≫
        compDiag gens e₃ m₂ q Z := by
  rw [compDiag_comp]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [compDiag_comp]

/-- The entry of the left side of the braid relation. -/
theorem compDiag_braidLeft (gens : P.Generators) (i j k' : I) (ν : X)
    (h : SKM.SChain [up i, up j, up k']
      (SKM.crossL [] i j [up k'] ++ SKM.crossL [up j] i k' [] ++ SKM.crossL [] j k' [up i])
      [up k', up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up k']) s t) (q : SPath (wd D ν [up k', up j, up i]) s t)
    (Z : P.H t) : compDiag gens (SKM.mkD D ν _ h) p q Z = braidLeft gens i j k' ν p q Z := by
  classical
  rw [show SKM.mkD D ν _ h = (SKM.mkD D ν (SKM.crossL [] i j [up k'])
      (sChain_crossL_whisker [] i j [up k']) ≫ SKM.mkD D ν (SKM.crossL [up j] i k' [])
      (sChain_crossL_whisker [up j] i k' [])) ≫ SKM.mkD D ν (SKM.crossL [] j k' [up i])
      (sChain_crossL_whisker [] j k' [up i]) by
    rw [SKM.mkD_comp, SKM.mkD_comp]]
  exact compDiag_comp_comp gens _ _ _ _ _ Z

/-- The entry of the right side of the braid relation. -/
theorem compDiag_braidRight (gens : P.Generators) (i j k' : I) (ν : X)
    (h : SKM.SChain [up i, up j, up k']
      (SKM.crossL [up i] j k' [] ++ SKM.crossL [] i k' [up j] ++ SKM.crossL [up k'] i j [])
      [up k', up j, up i]) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up k']) s t) (q : SPath (wd D ν [up k', up j, up i]) s t)
    (Z : P.H t) : compDiag gens (SKM.mkD D ν _ h) p q Z = braidRight gens i j k' ν p q Z := by
  classical
  rw [show SKM.mkD D ν _ h = (SKM.mkD D ν (SKM.crossL [up i] j k' [])
      (sChain_crossL_whisker [up i] j k' []) ≫ SKM.mkD D ν (SKM.crossL [] i k' [up j])
      (sChain_crossL_whisker [] i k' [up j])) ≫ SKM.mkD D ν (SKM.crossL [up k'] i j [])
      (sChain_crossL_whisker [up k'] i j []) by
    rw [SKM.mkD_comp, SKM.mkD_comp]]
  exact compDiag_comp_comp gens _ _ _ _ _ Z

open Classical in
/-- The entry of `n` dots on the third strand of `Eᵢ Eⱼ Eᵢ`. -/
theorem compDiag_dotsThird (gens : P.Generators) (i j : I) (ν : X) (n : ℕ) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dotsL [up i, up j] i [] n)
      (SKM.sChain_dotsL [up i, up j] i [] n)) p q Z =
      if hpq : p = q then compPow (dotEntry gens ν [up i, up j] i [] p Z) n ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 :=
  compList_dotsL gens ν [up i, up j] i [] n _ p q Z

open Classical in
/-- The entry of `n` dots on the second strand of `Eᵢ Eⱼ Eᵢ`. -/
theorem compDiag_dotsSecond (gens : P.Generators) (i j : I) (ν : X) (n : ℕ) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dotsL [up i] j [up i] n)
      (SKM.sChain_dotsL [up i] j [up i] n)) p q Z =
      if hpq : p = q then compPow (dotEntry gens ν [up i] j [up i] p Z) n ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 :=
  compList_dotsL gens ν [up i] j [up i] n _ p q Z

open Classical in
/-- The entry of `n` dots on the first strand of `Eᵢ Eⱼ Eᵢ`. -/
theorem compDiag_dotsFirst (gens : P.Generators) (i j : I) (ν : X) (n : ℕ) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dotsL [] i [up j, up i] n)
      (SKM.sChain_dotsL [] i [up j, up i] n)) p q Z =
      if hpq : p = q then compPow (dotEntry gens ν [] i [up j, up i] p Z) n ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 :=
  compList_dotsL gens ν [] i [up j, up i] n _ p q Z

open Classical in
/-- The entry of `a` dots on the third strand of `Eᵢ Eⱼ Eᵢ` followed by `b` dots on the first:
diagonal. -/
theorem compDiag_dots_dots (gens : P.Generators) (i j : I) (ν : X) (a b : ℕ)
    (h : SKM.SChain [up i, up j, up i]
      (SKM.dotsL [up i, up j] i [] a ++ SKM.dotsL [] i [up j, up i] b) [up i, up j, up i])
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z =
      if hpq : p = q then (compPow (dotEntry gens ν [up i, up j] i [] p Z) a ≫
        compPow (dotEntry gens ν [] i [up j, up i] p Z) b) ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 := by
  rw [show SKM.mkD D ν _ h = SKM.mkD D ν (SKM.dotsL [up i, up j] i [] a)
      (SKM.sChain_dotsL [up i, up j] i [] a) ≫
      SKM.mkD D ν (SKM.dotsL [] i [up j, up i] b) (SKM.sChain_dotsL [] i [up j, up i] b)
      from (SKM.mkD_comp D ν _ _ _ _).symm]
  rw [compDiag_comp]
  refine (Finset.sum_eq_single p (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_dotsThird gens i j ν a p m Z]
    simp [Ne.symm hm]
  erw [compDiag_dotsThird gens i j ν a p p Z, compDiag_dotsFirst gens i j ν b p q Z]
  by_cases hpq : p = q
  · subst hpq
    simp
  · simp [hpq]

open Classical in
/-- The entry of `a` dots on the third strand of `Eᵢ Eⱼ Eᵢ`, then `c` dots on the second, then
`b` dots on the first: diagonal. -/
theorem compDiag_dots_dots_dots (gens : P.Generators) (i j : I) (ν : X) (a c b : ℕ)
    (h : SKM.SChain [up i, up j, up i]
      (SKM.dotsL [up i, up j] i [] a ++ SKM.dotsL [up i] j [up i] c ++
        SKM.dotsL [] i [up j, up i] b) [up i, up j, up i])
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z =
      if hpq : p = q then (compPow (dotEntry gens ν [up i, up j] i [] p Z) a ≫
        compPow (dotEntry gens ν [up i] j [up i] p Z) c ≫
        compPow (dotEntry gens ν [] i [up j, up i] p Z) b) ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 := by
  rw [show SKM.mkD D ν _ h = (SKM.mkD D ν (SKM.dotsL [up i, up j] i [] a)
      (SKM.sChain_dotsL [up i, up j] i [] a) ≫
      SKM.mkD D ν (SKM.dotsL [up i] j [up i] c) (SKM.sChain_dotsL [up i] j [up i] c)) ≫
      SKM.mkD D ν (SKM.dotsL [] i [up j, up i] b) (SKM.sChain_dotsL [] i [up j, up i] b) by
    rw [SKM.mkD_comp, SKM.mkD_comp]]
  rw [compDiag_comp]
  refine (Finset.sum_eq_single q (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_dotsFirst gens i j ν b m q Z]
    simp [hm]
  rw [compDiag_comp, Preadditive.sum_comp]
  refine (Finset.sum_eq_single p (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_dotsThird gens i j ν a p m Z]
    simp [Ne.symm hm]
  erw [compDiag_dotsThird gens i j ν a p p Z, compDiag_dotsSecond gens i j ν c p q Z,
    compDiag_dotsFirst gens i j ν b q q Z]
  by_cases hpq : p = q
  · subst hpq
    simp [Category.assoc]
  · simp [hpq]

open Classical in
/-- **The braid relations (1.9) for the crossing and dot images**, entry by entry: the entries
`braidLeft` and `braidRight` of the two composites of three crossings agree unless
`i = k ≠ j`; for `i = k ≠ j` they agree off the diagonal and differ on the diagonal by the
correction terms of `braidEq`. -/
structure CrossBraid (gens : P.Generators) : Prop where
  /-- (1.9) for `Eᵢ Eⱼ Eₖ` unless `i = k ≠ j`. -/
  braid : ∀ (i j k' : I) (ν : X), ¬(i = k' ∧ i ≠ j) → ∀ {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up k']) s t) (q : SPath (wd D ν [up k', up j, up i]) s t)
    (Z : P.H t), braidLeft gens i j k' ν p q Z = braidRight gens i j k' ν p q Z
  /-- (1.9) for `Eᵢ Eⱼ Eᵢ`, `i ≠ j`, off the diagonal. -/
  braidEq_offDiag : ∀ (i j : I) (ν : X), i ≠ j → ∀ {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t), p ≠ q →
    braidLeft gens i j i ν p q Z = braidRight gens i j i ν p q Z
  /-- (1.9) for `Eᵢ Eⱼ Eᵢ`, `i ≠ j`, on the diagonal: the correction terms of `braidEq`. -/
  braidEq_diag : ∀ (i j : I) (ν : X), i ≠ j → ∀ {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t),
    braidLeft gens i j i ν p p Z - braidRight gens i j i ν p p Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry gens ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry gens ν [] i [up j, up i] p Z) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
          (compPow (dotEntry gens ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry gens ν [up i] j [up i] p Z) c ≫
            compPow (dotEntry gens ν [] i [up j, up i] p Z) (b - 1 - a))

variable {Gs Ys : ∀ s, P.H s}

/-- **`BraidRelations` for the swapped layer representation**: the braid relations (1.9) hold,
whiskered arbitrarily, as soon as the crossing and dot images satisfy `CrossBraid`. -/
theorem braidRelations {gens : P.Generators} (hb : CrossBraid gens) :
    BraidRelations Sc (P.layerRep Gs Ys gens) := by
  classical
  intro r hr
  cases r with
  | braid i j k' ν h =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up j, up k']) (b := SKM.ob D ν [up k', up j, up i])
      (SKM.relation D Sc (.braid i j k' ν h)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_of, compEval_of]
    erw [compDiag_braidLeft gens i j k' ν _ p q Z, compDiag_braidRight gens i j k' ν _ p q Z]
    rw [hb.braid i j k' ν h p q Z]
    exact sub_self _
  | braidEq i j ν hij =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up j, up i]) (b := SKM.ob D ν [up i, up j, up i])
      (SKM.relation D Sc (.braidEq i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_sub, compEval_sub, compEval_of, compEval_of, compEval_sum,
      compEval_sum]
    have h₁ : ∀ a ∈ Finset.range (D.dn i j), compEval gens
        ((zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          SKM.dg D ν (SKM.dotsL [up i, up j] i [] a ++ SKM.dotsL [] i [up j, up i]
            (D.dn i j - 1 - a))
            ((SKM.sChain_dotsL [up i, up j] i [] a).append
              (SKM.sChain_dotsL [] i [up j, up i] _))) p q Z =
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (if hpq : p = q then (compPow (dotEntry gens ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry gens ν [] i [up j, up i] p Z) (D.dn i j - 1 - a)) ≫
            eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0) := by
      intro a _
      rw [compEval_smul, compEval_of]
      erw [compDiag_dots_dots gens i j ν a _ _ p q Z]
    have h₂ : ∀ b ∈ Finset.Ioo 0 (D.dn i j), ∀ c ∈ Finset.Ioo 0 (D.dn j i),
        ∀ a ∈ Finset.range b, compEval gens
        ((zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
          SKM.dg D ν (SKM.dotsL [up i, up j] i [] a ++ SKM.dotsL [up i] j [up i] c ++
              SKM.dotsL [] i [up j, up i] (b - 1 - a))
            (((SKM.sChain_dotsL [up i, up j] i [] a).append
              (SKM.sChain_dotsL [up i] j [up i] c)).append
              (SKM.sChain_dotsL [] i [up j, up i] _))) p q Z =
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
          (if hpq : p = q then (compPow (dotEntry gens ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry gens ν [up i] j [up i] p Z) c ≫
            compPow (dotEntry gens ν [] i [up j, up i] p Z) (b - 1 - a)) ≫
            eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0) := by
      intro b _ c _ a _
      rw [compEval_smul, compEval_of]
      erw [compDiag_dots_dots_dots gens i j ν a c _ _ p q Z]
    rw [Finset.sum_congr rfl h₁, Finset.sum_congr rfl fun b hb => (compEval_sum gens _ _ p q Z).trans
      (Finset.sum_congr rfl fun c hc => (compEval_sum gens _ _ p q Z).trans
        (Finset.sum_congr rfl (h₂ b hb c hc)))]
    erw [compDiag_braidLeft gens i j i ν _ p q Z, compDiag_braidRight gens i j i ν _ p q Z]
    by_cases hpq : p = q
    · subst hpq
      simp only [dite_true, eqToHom_refl, Category.comp_id]
      rw [hb.braidEq_diag i j ν hij p Z]
      abel
    · rw [hb.braidEq_offDiag i j ν hij p q Z hpq]
      simp [hpq]
  | _ => simp [relGroup] at hr

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly

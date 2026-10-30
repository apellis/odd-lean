/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeSector
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff

/-! # Adjacent repeated-colour mixed-sector support

Supporting finite-sum reductions for Brundan–Ellis (1.9), in the component
`Rᵢ Pᵢ Pⱼ → Pⱼ Rᵢ Pᵢ`. Repeated colours give two paths with the same endpoints.
This module does not yet prove the braid component. The exact remaining obligations
are to specialize the displayed sums to `Rᵢ Pᵢ Pⱼ → Pⱼ Rᵢ Pᵢ`, kill the
three off-route terms on each side using the literal distinct crossing entries,
and identify the remaining products with `a_source ≫ R` and `R ≫ a_target`.
Here `R` contains the prescribed probe crossing and Q-weighted inverse mixed
interchange; the parameter polynomial must be retained, not cancelled.
One must derive unsigned transport of both repeated-colour dots through this
actual two-crossing map from the local and spectator slides (each sign occurs
twice), then transport the even inverse or odd unit denominator. No such dot
transport or braid is a hypothesis of any theorem below.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u
variable {I X : Type u} [AddCommGroup X] {D : Datum I X}
namespace ProbeReservoir

/-- The `i i j` endpoint supports exactly the two placements of the reservoir
among the repeated colour, rather than a unique path. -/
theorem adjacentMixed_iij_cases {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, j) true (nextSector (true, i) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, j) true (nextSector (true, i) false
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up i, up j]) s t) :
    p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) false true true hR trivial trivial e₀ ∨
      p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) true false true trivial hR trivial e₁ := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have hi := congrArg (fun x : Sector I => x.1 i) (e.trans e₀.symm)
  have hj := congrArg (fun x : Sector I => x.1 j) (e.trans e₀.symm)
  cases a <;> cases b <;> cases c <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      (exfalso; simp [nextSector, hij, Ne.symm hij] at hi hj)

/-- The middle word `i j i` has two paths in this occupied endpoint. -/
theorem adjacentMixed_iji_cases {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up i]) s t) :
    p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false true true hR trivial trivial e₀ ∨
      p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₁ := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have hi := congrArg (fun x : Sector I => x.1 i) (e.trans e₀.symm)
  have hj := congrArg (fun x : Sector I => x.1 j) (e.trans e₀.symm)
  cases a <;> cases b <;> cases c <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      (exfalso; simp [nextSector, hij, Ne.symm hij] at hi hj)

/-- The target word `j i i` still supports both repeated-colour placements. -/
theorem adjacentMixed_jii_cases {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, i) true (nextSector (true, i) false
      (nextSector (true, j) true s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, i) true
      (nextSector (true, j) true s)) = t)
    (p : SPath (wd D ν [up j, up i, up i]) s t) :
    p = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true false true trivial hR trivial e₀ ∨
      p = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₁ := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have hi := congrArg (fun x : Sector I => x.1 i) (e.trans e₀.symm)
  have hj := congrArg (fun x : Sector I => x.1 j) (e.trans e₀.symm)
  cases a <;> cases b <;> cases c <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      (exfalso; simp [nextSector, hij, Ne.symm hij] at hi hj)

theorem adjacentMixed_iij_sum {M : Type*} [AddCommMonoid M] {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, j) true (nextSector (true, i) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, j) true (nextSector (true, i) false
      (nextSector (true, i) true s)) = t)
    (f : SPath (wd D ν [up i, up i, up j]) s t → M) :
    let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
    ∑ p, f p = f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) false true true hR trivial trivial e₀) + f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) true false true trivial hR trivial e₁) := by
  classical
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
  refine Fintype.sum_eq_add _ _ (by intro h; cases h) ?_
  intro p hp
  rcases adjacentMixed_iij_cases hij hR e₀ e₁ p with h | h
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)

theorem adjacentMixed_iji_sum {M : Type*} [AddCommMonoid M] {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (f : SPath (wd D ν [up i, up j, up i]) s t → M) :
    let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up i]) s t)
    ∑ p, f p = f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false true true hR trivial trivial e₀) + f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₁) := by
  classical
  let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up i]) s t)
  refine Fintype.sum_eq_add _ _ (by intro h; cases h) ?_
  intro p hp
  rcases adjacentMixed_iji_cases hij hR e₀ e₁ p with h | h
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)

theorem adjacentMixed_jii_sum {M : Type*} [AddCommMonoid M] {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, i) true (nextSector (true, i) false
      (nextSector (true, j) true s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, i) true
      (nextSector (true, j) true s)) = t)
    (f : SPath (wd D ν [up j, up i, up i]) s t → M) :
    let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
    ∑ p, f p = f (SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true false true trivial hR trivial e₀) + f (SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₁) := by
  classical
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
  refine Fintype.sum_eq_add _ _ (by intro h; cases h) ?_
  intro p hp
  rcases adjacentMixed_jii_cases hij hR e₀ e₁ p with h | h
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)


variable {k : Type u} [CommRing k] {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] {Sc : Scalars D k}

/-- The supplied inverse identities determine the actual mixed coefficient.
At odd colour this uses the genuine unit denominator from `CrossCoeffInputs`,
not cancellation of a crossing or a Q polynomial. -/
theorem adjacentMixed_coeff_unique (P : ProbeReservoir k B D Sc)
    (c d : P.CrossCoeff Sc) (hc : c.IsInverse) (hd : d.IsInverse)
    (h : P.CrossCoeffInputs) (i : I) (s : Sector I)
    (hv : StepValid (true, i) false s)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false s))) :
    c.a i s hv Z = d.a i s hv Z := by
  by_cases hi : D.parity i = 0
  · calc
      c.a i s hv Z = c.a i s hv Z ≫
          ((P.rpPostDot i s hv Z - P.rpPreDot i s hv Z) ≫ d.a i s hv Z) := by
        rw [(hd.even i hi s hv Z).2, Category.comp_id]
      _ = d.a i s hv Z := by
        rw [← Category.assoc, (hc.even i hi s hv Z).1, Category.id_comp]
  · have hi' : D.parity i = 1 := by
      rcases (show D.parity i = 0 ∨ D.parity i = 1 by
        generalize D.parity i = p; fin_cases p
        · exact Or.inl rfl
        · exact Or.inr rfl) with h' | h'
      · exact False.elim (hi h')
      · exact h'
    let v := P.crossDenom h i s hv Z
    have hv' : (v : End (P.rpObj i i s hv Z)) =
        P.rpPreDot i s hv Z ≫ P.rpPreDot i s hv Z -
          P.rpPostDot i s hv Z ≫ P.rpPostDot i s hv Z := by
      simp [v, crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have he : c.a i s hv Z ≫ (v : End (P.rpObj i i s hv Z)) =
        d.a i s hv Z ≫ (v : End (P.rpObj i i s hv Z)) := by
      rw [hv', (hc.odd i hi' s hv Z).1, (hd.odd i hi' s hv Z).1]
    have hcancel := congrArg (fun f => f ≫
      ((v⁻¹ : (End (P.rpObj i i s hv Z))ˣ) : End (P.rpObj i i s hv Z))) he
    have hinv : (v : End (P.rpObj i i s hv Z)) ≫
        ((v⁻¹ : (End (P.rpObj i i s hv Z))ˣ) : End (P.rpObj i i s hv Z)) = 𝟙 _ := by
      rw [← End.mul_def, Units.inv_mul]
      rfl
    simpa only [Category.assoc, hinv, Category.comp_id] using hcancel


/-- Literal left braid sum at the occupied mixed endpoint: four terms before
using the off-diagonal zeros of the distinct-colour crossings. -/
theorem adjacentMixed_braidLeft_sum (P : ProbeReservoir k B D Sc)
    (gens : P.Generators) (ν : X) (i j : I) (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, j) true (nextSector (true, i) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, j) true (nextSector (true, i) false
      (nextSector (true, i) true s)) = t)
    (e₂ : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false s)) = t)
    (e₃ : nextSector (true, i) false (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t) (Z : P.H t) :
    let a : SPath (wd D ν [up i, up i, up j]) s t := SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) false true true hR trivial trivial e₀
    let b : SPath (wd D ν [up i, up i, up j]) s t := SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) true false true trivial hR trivial e₁
    let x : SPath (wd D ν [up i, up j, up i]) s t := SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false true true hR trivial trivial e₂
    let y : SPath (wd D ν [up i, up j, up i]) s t := SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₃
    braidLeft gens i i j ν p q Z =
      (crossEntry gens ν [] i i [up j] p a Z ≫ crossEntry gens ν [up i] i j [] a x Z +
        crossEntry gens ν [] i i [up j] p b Z ≫ crossEntry gens ν [up i] i j [] b x Z) ≫
          crossEntry gens ν [] i j [up i] x q Z +
      (crossEntry gens ν [] i i [up j] p a Z ≫ crossEntry gens ν [up i] i j [] a y Z +
        crossEntry gens ν [] i i [up j] p b Z ≫ crossEntry gens ν [up i] i j [] b y Z) ≫
          crossEntry gens ν [] i j [up i] y q Z := by
  classical
  dsimp only
  unfold braidLeft
  refine (adjacentMixed_iji_sum hij hR e₂ e₃ _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg (fun f => f ≫ _) (adjacentMixed_iij_sum hij hR e₀ e₁ _)
  · exact congrArg (fun f => f ≫ _) (adjacentMixed_iij_sum hij hR e₀ e₁ _)

/-- Literal right braid sum at the occupied mixed endpoint: four terms before
using the off-diagonal zeros of the distinct-colour crossings. -/
theorem adjacentMixed_braidRight_sum (P : ProbeReservoir k B D Sc)
    (gens : P.Generators) (ν : X) (i j : I) (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (e₀ : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (e₂ : nextSector (true, i) true (nextSector (true, i) false
      (nextSector (true, j) true s)) = t)
    (e₃ : nextSector (true, i) false (nextSector (true, i) true
      (nextSector (true, j) true s)) = t)
    (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t) (Z : P.H t) :
    let a : SPath (wd D ν [up i, up j, up i]) s t := SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false true true hR trivial trivial e₀
    let b : SPath (wd D ν [up i, up j, up i]) s t := SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₁
    let x : SPath (wd D ν [up j, up i, up i]) s t := SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true false true trivial hR trivial e₂
    let y : SPath (wd D ν [up j, up i, up i]) s t := SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true true false trivial trivial hR e₃
    braidRight gens i i j ν p q Z =
      (crossEntry gens ν [up i] i j [] p a Z ≫ crossEntry gens ν [] i j [up i] a x Z +
        crossEntry gens ν [up i] i j [] p b Z ≫ crossEntry gens ν [] i j [up i] b x Z) ≫
          crossEntry gens ν [up j] i i [] x q Z +
      (crossEntry gens ν [up i] i j [] p a Z ≫ crossEntry gens ν [] i j [up i] a y Z +
        crossEntry gens ν [up i] i j [] p b Z ≫ crossEntry gens ν [] i j [up i] b y Z) ≫
          crossEntry gens ν [up j] i i [] y q Z := by
  classical
  dsimp only
  unfold braidRight
  refine (adjacentMixed_jii_sum hij hR e₂ e₃ _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg (fun f => f ≫ _) (adjacentMixed_iji_sum hij hR e₀ e₁ _)
  · exact congrArg (fun f => f ≫ _) (adjacentMixed_iji_sum hij hR e₀ e₁ _)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

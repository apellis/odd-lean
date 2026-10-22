/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.GradedWalk
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Int.Interval

/-!
# Degree-zero corners of supercommuting products of local graded rings

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. An indecomposable summand of `E_𝐢 F_𝐢′ 1_λ` of maximal width is cut out by an
idempotent `α(e) α′(e′)`, where `e`, `e′` are primitive idempotents of quiver Hecke
superalgebras; modulo maps through shorter words, its degree-zero endomorphisms are spanned by
products `α(x) α′(y)` of total degree zero. This file proves that such a span is local in the
following form.

Let `E γ`, `F γ` (`γ ∈ ℤ × ℤ/2`, degree and parity) be graded families of `k`-submodules of a
`k`-algebra `R`, vanishing in degrees below `-lo`, with `F` supercommuting with `E`. Suppose
`E (0, 0)` has an identity `εE` and a nilpotent ideal `NE` with `E (0, 0) = k εE + NE`, and that
`E γ * E (-γ) ⊆ NE` for `γ ≠ 0` (no summand is isomorphic to a nonzero shift or parity shift of
itself); likewise for `F`. Then every element of `⨆ γ, E γ * F (-γ)` is `c • εE εF` plus a
nilpotent (`exists_isNilpotent_sub_smul`). The proof feeds the products `x y` into the walk lemma
`prod_eq_zero_of_walk`, graded by the degree of the `E`-factor.
-/

namespace OddMath.SKM.GradedWalk

open Finset
open scoped Pointwise

/-- Degree and parity. -/
abbrev Deg := ℤ × ZMod 2

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

/-- A graded family `E` of submodules whose degree-zero part is local with identity `ε` and
nilpotent radical `NE` (`NE ^ a = ⊥`), vanishing below degree `-lo`, and with
`E γ * E (-γ) ⊆ NE` for `γ ≠ 0`. -/
structure LocalCorner (E : Deg → Submodule k R) (ε : R) (NE : Submodule k R) (a lo : ℕ) :
    Prop where
  mul_le : ∀ γ δ, E γ * E δ ≤ E (γ + δ)
  unit_mem : ε ∈ E 0
  unit_mul : ∀ x ∈ E 0, ε * x = x
  mul_unit : ∀ x ∈ E 0, x * ε = x
  rad_le : NE ≤ E 0
  mul_rad : E 0 * NE ≤ NE
  rad_mul : NE * E 0 ≤ NE
  rad_pow : NE ^ a = ⊥
  residue : ∀ x ∈ E 0, ∃ c : k, x - c • ε ∈ NE
  pair_le : ∀ γ, γ ≠ 0 → E γ * E (-γ) ≤ NE
  eq_bot : ∀ γ : Deg, γ.1 < -(lo : ℤ) → E γ = ⊥

/-- `F` supercommutes with `E`. -/
def SuperComm (E F : Deg → Submodule k R) : Prop :=
  ∀ {γ δ : Deg} {x y : R}, x ∈ E γ → y ∈ F δ →
    y * x = if γ.2 = 1 ∧ δ.2 = 1 then -(x * y) else x * y

variable {E F : Deg → Submodule k R} {εE εF : R} {NE NF : Submodule k R} {a b lo : ℕ}

theorem SuperComm.zero_right (hc : SuperComm E F) {γ : Deg} {x y : R} (hx : x ∈ E γ)
    (hy : y ∈ F 0) : y * x = x * y := by
  rw [hc hx hy]; simp [show (0 : ZMod 2) ≠ 1 by decide]

theorem SuperComm.zero_left (hc : SuperComm E F) {δ : Deg} {x y : R} (hx : x ∈ E 0)
    (hy : y ∈ F δ) : y * x = x * y := by
  rw [hc hx hy]; simp [show (0 : ZMod 2) ≠ 1 by decide]

theorem SuperComm.mul_pair (hc : SuperComm E F) {γ δ : Deg} {x y x' y' : R} (hx' : x' ∈ E γ)
    (hy : y ∈ F δ) :
    x * y * (x' * y') = x * x' * (y * y') ∨ x * y * (x' * y') = -(x * x' * (y * y')) := by
  have h := hc hx' hy
  have e : x * y * (x' * y') = x * (y * x') * y' := by simp only [mul_assoc]
  rw [e, h]
  split_ifs
  · right; simp only [mul_neg, neg_mul, mul_assoc]
  · left; simp only [mul_assoc]

theorem LocalCorner.mem_zero_of_mem {E : Deg → Submodule k R} {ε : R} {NE : Submodule k R}
    (hE : LocalCorner E ε NE a lo) {γ δ : Deg} {x x' : R} (hx : x ∈ E γ) (hx' : x' ∈ E δ) :
    x * x' ∈ E (γ + δ) :=
  hE.mul_le γ δ (Submodule.mul_mem_mul hx hx')

theorem LocalCorner.pow_mul_le {E : Deg → Submodule k R} {ε : R} {NE : Submodule k R}
    (hE : LocalCorner E ε NE a lo) (i : ℕ) : NE ^ i * E 0 ≤ E 0 := by
  induction i with
  | zero => rw [pow_zero, one_mul]
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact (mul_le_mul' le_rfl ih).trans (hE.rad_mul.trans hE.rad_le)

theorem LocalCorner.mul_pow_mul_le {E : Deg → Submodule k R} {ε : R} {NE : Submodule k R}
    (hE : LocalCorner E ε NE a lo) (i : ℕ) : E 0 * (NE ^ i * E 0) ≤ NE ^ i * E 0 := by
  cases i with
  | zero =>
    rw [pow_zero, one_mul]
    simpa using hE.mul_le 0 0
  | succ i =>
    calc E 0 * (NE ^ (i + 1) * E 0) = E 0 * NE * (NE ^ i * E 0) := by
          rw [pow_succ', mul_assoc NE, mul_assoc]
      _ ≤ NE * (NE ^ i * E 0) := mul_le_mul' hE.mul_rad le_rfl
      _ = NE ^ (i + 1) * E 0 := by rw [pow_succ', mul_assoc]

theorem LocalCorner.pow_mul_eq_bot {E : Deg → Submodule k R} {ε : R} {NE : Submodule k R}
    (hE : LocalCorner E ε NE a lo) {i : ℕ} (hi : a ≤ i) : NE ^ i * E 0 = ⊥ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [pow_add, hE.rad_pow, Submodule.bot_mul, Submodule.bot_mul]

/-- Products `x y` with `x ∈ E γ`, `y ∈ F (-γ)` (and `1` in degree zero). -/
def pairSet (E F : Deg → Submodule k R) (γ : Deg) : Set R :=
  {r | (∃ x ∈ E γ, ∃ y ∈ F (-γ), r = x * y) ∨ (γ = 0 ∧ r = 1)}

/-- Degree-zero products with a radical factor. -/
def radSet (E F : Deg → Submodule k R) (NE NF : Submodule k R) : Set R :=
  {r | ∃ x y, ((x ∈ NE ∧ y ∈ F 0) ∨ (x ∈ E 0 ∧ y ∈ NF)) ∧ r = x * y}

/-- Products of total degree zero that are not units: a nonzero `E`-degree, or a radical
factor. -/
def smallSet (E F : Deg → Submodule k R) (NE NF : Submodule k R) : Set R :=
  {r | (∃ γ : Deg, γ ≠ 0 ∧ ∃ x ∈ E γ, ∃ y ∈ F (-γ), r = x * y) ∨ r ∈ radSet E F NE NF}

theorem radSet_spec (hE : LocalCorner E εE NE a lo) (hF : LocalCorner F εF NF b lo)
    {r : R} (hr : r ∈ radSet E F NE NF) : ∃ x ∈ E 0, ∃ y ∈ F 0, r = x * y := by
  obtain ⟨x, y, h | h, rfl⟩ := hr
  · exact ⟨x, hE.rad_le h.1, y, h.2, rfl⟩
  · exact ⟨x, h.1, y, hF.rad_le h.2, rfl⟩

/-- Products of at least `a + b + 1` elements of `radSet` vanish. -/
theorem radSet_prod_aux (hE : LocalCorner E εE NE a lo) (hF : LocalCorner F εF NF b lo)
    (hc : SuperComm E F) :
    ∀ l : List R, (∀ r ∈ l, r ∈ radSet E F NE NF) → ∃ i j : ℕ, l.length ≤ i + j ∧
      ∃ X ∈ NE ^ i * E 0, ∃ Y ∈ NF ^ j * F 0, εE * εF * l.prod = X * Y
  | [], _ => ⟨0, 0, le_rfl, εE, by simpa using hE.unit_mem, εF, by simpa using hF.unit_mem,
      by simp⟩
  | r :: l, hl => by
    obtain ⟨i, j, hij, X, hX, Y, hY, he⟩ := radSet_prod_aux hE hF hc l (fun s hs =>
      hl s (List.mem_cons_of_mem r hs))
    obtain ⟨x, y, hxy, rfl⟩ := hl r List.mem_cons_self
    have hx0 : x ∈ E 0 := hxy.elim (fun h => hE.rad_le h.1) (fun h => h.1)
    have hy0 : y ∈ F 0 := hxy.elim (fun h => h.2) (fun h => hF.rad_le h.2)
    have hX0 : X ∈ E 0 := hE.pow_mul_le i hX
    have hY0 : Y ∈ F 0 := hF.pow_mul_le j hY
    have hlead : εE * εF * (x * y) = x * y := calc
      εE * εF * (x * y) = εE * (εF * x) * y := by simp only [mul_assoc]
      _ = (εE * x) * (εF * y) := by rw [hc.zero_left hx0 hF.unit_mem]; simp only [mul_assoc]
      _ = x * y := by rw [hE.unit_mul x hx0, hF.unit_mul y hy0]
    have htail : x * y * (εE * εF) = x * y := calc
      x * y * (εE * εF) = x * (y * εE) * εF := by simp only [mul_assoc]
      _ = (x * εE) * (y * εF) := by rw [hc.zero_left hE.unit_mem hy0]; simp only [mul_assoc]
      _ = x * y := by rw [hE.mul_unit x hx0, hF.mul_unit y hy0]
    have hprod : εE * εF * (x * y * l.prod) = x * X * (y * Y) := calc
      εE * εF * (x * y * l.prod) = x * y * (εE * εF * l.prod) := by
        rw [← mul_assoc, hlead, ← mul_assoc (x * y), htail]
      _ = x * (y * X) * Y := by rw [he]; simp only [mul_assoc]
      _ = x * X * (y * Y) := by rw [hc.zero_right hX0 hy0]; simp only [mul_assoc]
    rcases hxy with ⟨hxN, -⟩ | ⟨-, hyN⟩
    · refine ⟨i + 1, j, by simp; omega, x * X, ?_, y * Y, ?_, by simpa using hprod⟩
      · rw [pow_succ', mul_assoc]; exact Submodule.mul_mem_mul hxN hX
      · exact hF.mul_pow_mul_le j (Submodule.mul_mem_mul hy0 hY)
    · refine ⟨i, j + 1, by simp; omega, x * X, ?_, y * Y, ?_, by simpa using hprod⟩
      · exact hE.mul_pow_mul_le i (Submodule.mul_mem_mul hx0 hX)
      · rw [pow_succ', mul_assoc]; exact Submodule.mul_mem_mul hyN hY

theorem radSet_prod (hE : LocalCorner E εE NE a lo) (hF : LocalCorner F εF NF b lo)
    (hc : SuperComm E F) (l : List R) (hlen : l.length = a + b + 1)
    (hl : ∀ r ∈ l, r ∈ radSet E F NE NF) : l.prod = 0 := by
  obtain ⟨i, j, hij, X, hX, Y, hY, he⟩ := radSet_prod_aux hE hF hc l hl
  have hlead : εE * εF * l.prod = l.prod := by
    obtain ⟨r, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain ⟨x, hx0, y, hy0, rfl⟩ := radSet_spec hE hF (hl r List.mem_cons_self)
    calc εE * εF * (x * y * l'.prod) = εE * (εF * x) * y * l'.prod := by
          simp only [mul_assoc]
      _ = (εE * x) * (εF * y) * l'.prod := by
          rw [hc.zero_left hx0 hF.unit_mem]; simp only [mul_assoc]
      _ = (x * y :: l').prod := by
          rw [hE.unit_mul x hx0, hF.unit_mul y hy0, List.prod_cons, mul_assoc]
  rw [← hlead, he]
  rcases le_or_gt a i with hi | hi
  · rw [hE.pow_mul_eq_bot hi, Submodule.mem_bot] at hX
    rw [hX, zero_mul]
  · rw [hF.pow_mul_eq_bot (show b ≤ j by omega), Submodule.mem_bot] at hY
    rw [hY, mul_zero]

theorem walk_pairSet (hE : LocalCorner E εE NE a lo) (hF : LocalCorner F εF NF b lo)
    (hc : SuperComm E F) :
    Walk (pairSet E F) (radSet E F NE NF) ((Icc (-(lo : ℤ)) lo) ×ˢ univ) (a + b + 1) where
  one_mem := Or.inr ⟨rfl, rfl⟩
  mul_mem := by
    intro γ δ r s hr hs
    rcases hr with ⟨x, hx, y, hy, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hs with ⟨x', hx', y', hy', rfl⟩ | ⟨rfl, rfl⟩
      · have hyy : y * y' ∈ F (-(γ + δ)) := by
          rw [neg_add]; exact hF.mem_zero_of_mem hy hy'
        have hxx := hE.mem_zero_of_mem hx hx'
        refine Or.inl ?_
        rcases hc.mul_pair (x := x) (y' := y') hx' hy with h | h
        · exact ⟨_, hxx, _, hyy, by rw [h, mul_assoc]⟩
        · exact ⟨_, neg_mem hxx, _, hyy, by rw [h, neg_mul, mul_assoc]⟩
      · rw [mul_one, add_zero]; exact Or.inl ⟨x, hx, y, hy, rfl⟩
    · rw [one_mul, zero_add]; exact hs
  eq_zero := by
    intro γ r hγ hr
    rcases hr with ⟨x, hx, y, hy, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [mem_product, mem_Icc, mem_univ, and_true, not_and_or, not_le] at hγ
      rcases hγ with h | h
      · rw [hE.eq_bot γ h, Submodule.mem_bot] at hx; rw [hx, zero_mul]
      · rw [hF.eq_bot (-γ) (by simp; omega), Submodule.mem_bot] at hy; rw [hy, mul_zero]
    · exact absurd (by simp) hγ
  mul_mem_N := by
    intro r s hr hs
    rcases hs with ⟨x', hx', y', hy', rfl⟩ | ⟨-, rfl⟩
    · rw [neg_zero] at hy'
      obtain ⟨x, y, hxy, rfl⟩ := hr
      have hx0 : x ∈ E 0 := hxy.elim (fun h => hE.rad_le h.1) (fun h => h.1)
      have hy0 : y ∈ F 0 := hxy.elim (fun h => h.2) (fun h => hF.rad_le h.2)
      have e : x * y * (x' * y') = x * x' * (y * y') := by
        rw [mul_assoc, ← mul_assoc y, hc.zero_right hx' hy0]; simp only [mul_assoc]
      refine ⟨x * x', y * y', ?_, e⟩
      have hyy : y * y' ∈ F 0 := by simpa using hF.mem_zero_of_mem hy0 hy'
      rcases hxy with ⟨hxN, -⟩ | ⟨-, hyN⟩
      · exact Or.inl ⟨hE.rad_mul (Submodule.mul_mem_mul hxN hx'), hyy⟩
      · exact Or.inr ⟨by simpa using hE.mem_zero_of_mem hx0 hx',
          hF.rad_mul (Submodule.mul_mem_mul hyN hy')⟩
    · rw [mul_one]; exact hr
  pair_mem_N := by
    intro γ r s hγ hr hs
    rcases hr with ⟨x, hx, y, hy, rfl⟩ | ⟨h, -⟩
    · rcases hs with ⟨x', hx', y', hy', rfl⟩ | ⟨h, -⟩
      · rw [neg_neg] at hy'
        have hxx : x * x' ∈ NE := hE.pair_le γ hγ (Submodule.mul_mem_mul hx hx')
        have hyy : y * y' ∈ F 0 := by simpa using hF.mem_zero_of_mem hy hy'
        rcases hc.mul_pair (x := x) (y' := y') hx' hy with h | h
        · exact ⟨_, _, Or.inl ⟨hxx, hyy⟩, h⟩
        · exact ⟨_, _, Or.inl ⟨neg_mem hxx, hyy⟩, by rw [h, neg_mul]⟩
      · exact absurd (neg_eq_zero.mp h) hγ
    · exact absurd h hγ
  nil := radSet_prod hE hF hc

theorem smallSet_spec (hE : LocalCorner E εE NE a lo) (hF : LocalCorner F εF NF b lo)
    {r : R} (hr : r ∈ smallSet E F NE NF) :
    ∃ γ : Deg, r ∈ pairSet E F γ ∧ (γ ≠ 0 ∨ r ∈ radSet E F NE NF) := by
  rcases hr with ⟨γ, hγ, x, hx, y, hy, rfl⟩ | hr
  · exact ⟨γ, Or.inl ⟨x, hx, y, hy, rfl⟩, Or.inl hγ⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := radSet_spec hE hF hr
    exact ⟨0, Or.inl ⟨x, hx, y, by simpa using hy, rfl⟩, Or.inr hr⟩

/-- Long products of elements of `smallSet` vanish. -/
theorem smallSet_pow (hE : LocalCorner E εE NE a lo) (hF : LocalCorner F εF NF b lo)
    (hc : SuperComm E F) {L : ℕ} (hL : (2 * lo + 1) * 2 * (a + b + 1) < L + 1) {r : R}
    (hr : r ∈ smallSet E F NE NF ^ L) : r = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hr
  choose γ hγ using fun i : Fin L => smallSet_spec hE hF (f i).2
  let x : ℕ → R := fun t => if h : t < L then (f ⟨t, h⟩ : R) else 0
  let g : ℕ → Deg := fun t => if h : t < L then γ ⟨t, h⟩ else 0
  have hlist : (List.ofFn fun i => (f i : R)) = (List.range L).map x := by
    apply List.ext_getElem (by simp)
    intro t h₁ h₂
    have ht : t < L := by simpa using h₁
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, x, ht, ↓reduceDIte]
  rw [hlist]
  refine prod_eq_zero_of_walk (walk_pairSet hE hF hc) (g := g) (fun t ht => ?_) ?_
  · simp only [x, g, ht, ↓reduceDIte]
    exact hγ ⟨t, ht⟩
  · have hcard : #((Icc (-(lo : ℤ)) lo) ×ˢ (univ : Finset (ZMod 2))) = (2 * lo + 1) * 2 := by
      rw [card_product, Int.card_Icc]
      simp only [card_univ, ZMod.card]
      omega
    rw [hcard]; exact hL

/-- **Degree-zero corners are local.** Every element of `⨆ γ, E γ * F (-γ)` is a scalar multiple
of `εE * εF` plus a nilpotent element. -/
theorem exists_isNilpotent_sub_smul (hE : LocalCorner E εE NE a lo)
    (hF : LocalCorner F εF NF b lo) (hc : SuperComm E F) {z : R}
    (hz : z ∈ ⨆ γ, E γ * F (-γ)) : ∃ c : k, IsNilpotent (z - c • (εE * εF)) := by
  have hle : (⨆ γ, E γ * F (-γ)) ≤
      Submodule.span k {εE * εF} ⊔ Submodule.span k (smallSet E F NE NF) := by
    refine iSup_le fun γ => Submodule.mul_le.mpr fun x hx y hy => ?_
    by_cases hγ : γ = 0
    · subst hγ
      rw [neg_zero] at hy
      obtain ⟨c, hc⟩ := hE.residue x hx
      obtain ⟨c', hc'⟩ := hF.residue y hy
      set n := x - c • εE
      set n' := y - c' • εF
      have e : x * y = (c * c') • (εE * εF) + (c • (εE * n') + n * y) := by
        have hx' : x = c • εE + n := by simp [n]
        have hy' : y = c' • εF + n' := by simp [n']
        calc x * y = (c • εE + n) * y := by rw [← hx']
          _ = c • (εE * (c' • εF + n')) + n * y := by rw [add_mul, smul_mul_assoc, ← hy']
          _ = _ := by
            rw [mul_add, mul_smul_comm, smul_add, smul_smul, add_assoc]
      rw [e]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
        (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
          (Submodule.subset_span ?_))
      · exact Or.inr ⟨εE, n', Or.inr ⟨hE.unit_mem, hc'⟩, rfl⟩
      · exact Or.inr ⟨n, y, Or.inl ⟨hc, hy⟩, rfl⟩
    · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨γ, hγ, x, hx, y, hy, rfl⟩))
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (hle hz)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  refine ⟨c, (2 * lo + 1) * 2 * (a + b + 1), ?_⟩
  have hpow : w ^ ((2 * lo + 1) * 2 * (a + b + 1)) ∈
      Submodule.span k (smallSet E F NE NF ^ ((2 * lo + 1) * 2 * (a + b + 1))) := by
    rw [← Submodule.span_pow]; exact Submodule.pow_mem_pow _ hw _
  have hbot : Submodule.span k (smallSet E F NE NF ^ ((2 * lo + 1) * 2 * (a + b + 1))) = ⊥ :=
    Submodule.span_eq_bot.mpr fun r hr => smallSet_pow hE hF hc (Nat.lt_succ_self _) hr
  rw [hbot, Submodule.mem_bot] at hpow
  rw [add_sub_cancel_left]; exact hpow

end OddMath.SKM.GradedWalk

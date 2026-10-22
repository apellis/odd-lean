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
import Mathlib.Tactic.FinCases

/-!
# Products of supercommuting local graded families

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. An indecomposable summand of `E_𝐢 F_𝐢′ 1_λ` of maximal width is cut out by an
idempotent `α(e) α′(e′)`, where `e`, `e′` are primitive idempotents of quiver Hecke
superalgebras. Modulo maps through shorter words, its endomorphisms are spanned by products
`α(x) α′(y) β` with `β` a bubble in the rightmost region. This file proves that the degree-zero
part of such a span is local.

A `LocalCorner E ε NE a lo` is a family `E γ` (`γ ∈ ℤ × ℤ/2`, degree and parity) of
`k`-submodules of a `k`-algebra `R`, multiplicative, vanishing below degree `-lo`, with identity
`ε`, whose degree-zero part is `k ε + NE` for an ideal `NE` with `NE ^ a = ⊥`, and with
`E γ * E (-γ) ⊆ NE` for `γ ≠ 0`. For a primitive idempotent `e` of a graded superalgebra whose
degree-zero corner is local, `γ ↦ image of (e H e)_γ` is one, provided no summand is isomorphic
to a nonzero degree or parity shift of itself.

* `LocalCorner.mul`: if `F` supercommutes with `E`, the products `E δ * F (γ - δ)` form a local
  corner with identity `εE * εF` (`prodFam`). The radical is spanned by the products `x y` with
  `x ∈ E γ`, `y ∈ F (-γ)` that have a nonzero `E`-degree or a radical factor; they are nilpotent
  by the walk lemma `prod_eq_zero_of_walk`, graded by the degree of the `E`-factor.
* `SuperComm.prodFam`: a family supercommuting with `E` and `F` supercommutes with the products.
* `LocalCorner.exists_isNilpotent_sub_smul`: every degree-zero element is `c • ε` plus a
  nilpotent.
-/

namespace OddMath.SKM.GradedWalk

open Finset
open scoped Pointwise

/-- Degree and parity. -/
abbrev Deg := ℤ × ZMod 2

/-- The Koszul sign of two parities. -/
def ksign (p q : ZMod 2) : ℤ := if p = 1 ∧ q = 1 then -1 else 1

theorem ksign_zero_left (q : ZMod 2) : ksign 0 q = 1 := by fin_cases q <;> decide

theorem ksign_zero_right (p : ZMod 2) : ksign p 0 = 1 := by fin_cases p <;> decide

theorem ksign_add_left (p p' q : ZMod 2) : ksign (p + p') q = ksign p q * ksign p' q := by
  fin_cases p <;> fin_cases p' <;> fin_cases q <;> decide

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

/-- A graded family `E` of submodules, with identity `ε`, whose degree-zero part is local with
nilpotent radical `NE` (`NE ^ a = ⊥`), vanishing below degree `-lo`, and with
`E γ * E (-γ) ⊆ NE` for `γ ≠ 0`. -/
structure LocalCorner (E : Deg → Submodule k R) (ε : R) (NE : Submodule k R) (a lo : ℕ) :
    Prop where
  mul_le : ∀ γ δ, E γ * E δ ≤ E (γ + δ)
  unit_mem : ε ∈ E 0
  unit_mul : ∀ γ, ∀ x ∈ E γ, ε * x = x
  mul_unit : ∀ γ, ∀ x ∈ E γ, x * ε = x
  rad_le : NE ≤ E 0
  mul_rad : E 0 * NE ≤ NE
  rad_mul : NE * E 0 ≤ NE
  rad_pow : NE ^ a = ⊥
  residue : ∀ x ∈ E 0, ∃ c : k, x - c • ε ∈ NE
  pair_le : ∀ γ, γ ≠ 0 → E γ * E (-γ) ≤ NE
  eq_bot : ∀ γ : Deg, γ.1 < -(lo : ℤ) → E γ = ⊥

/-- `F` supercommutes with `E`. -/
def SuperComm (E F : Deg → Submodule k R) : Prop :=
  ∀ {γ δ : Deg} {x y : R}, x ∈ E γ → y ∈ F δ → y * x = ksign γ.2 δ.2 • (x * y)

variable {E F G : Deg → Submodule k R} {εE εF : R} {NE NF : Submodule k R} {a b loE loF : ℕ}

theorem SuperComm.zero_right (hc : SuperComm E F) {γ : Deg} {x y : R} (hx : x ∈ E γ)
    (hy : y ∈ F 0) : y * x = x * y := by
  rw [hc hx hy, Prod.snd_zero, ksign_zero_right, one_smul]

theorem SuperComm.zero_left (hc : SuperComm E F) {δ : Deg} {x y : R} (hx : x ∈ E 0)
    (hy : y ∈ F δ) : y * x = x * y := by
  rw [hc hx hy, Prod.snd_zero, ksign_zero_left, one_smul]

theorem SuperComm.mul_pair (hc : SuperComm E F) {γ δ : Deg} {x y x' y' : R} (hx' : x' ∈ E γ)
    (hy : y ∈ F δ) : x * y * (x' * y') = (ksign γ.2 δ.2 • (x * x')) * (y * y') := by
  rw [show x * y * (x' * y') = x * (y * x') * y' by simp only [mul_assoc], hc hx' hy]
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]

/-- A family supercommuting with `E` and `F` supercommutes with their products. -/
theorem SuperComm.prodFam_aux (hEG : SuperComm E G) (hFG : SuperComm F G) {γ δ δ₁ : Deg}
    {x₁ x₂ y : R} (hx₁ : x₁ ∈ E δ₁) (hx₂ : x₂ ∈ F (γ - δ₁)) (hy : y ∈ G δ) :
    y * (x₁ * x₂) = ksign γ.2 δ.2 • (x₁ * x₂ * y) := by
  have hs : δ₁.2 + (γ - δ₁).2 = γ.2 := by simp
  calc y * (x₁ * x₂) = y * x₁ * x₂ := (mul_assoc _ _ _).symm
    _ = ksign δ₁.2 δ.2 • (x₁ * (y * x₂)) := by rw [hEG hx₁ hy, smul_mul_assoc, mul_assoc]
    _ = ksign γ.2 δ.2 • (x₁ * x₂ * y) := by
      rw [hFG hx₂ hy, mul_smul_comm, smul_smul, ← ksign_add_left, hs, mul_assoc]

theorem LocalCorner.mul_mem (hE : LocalCorner E εE NE a loE) {γ δ : Deg} {x x' : R}
    (hx : x ∈ E γ) (hx' : x' ∈ E δ) : x * x' ∈ E (γ + δ) :=
  hE.mul_le γ δ (Submodule.mul_mem_mul hx hx')

theorem LocalCorner.pow_mul_le (hE : LocalCorner E εE NE a loE) (i : ℕ) :
    NE ^ i * E 0 ≤ E 0 := by
  induction i with
  | zero => rw [pow_zero, one_mul]
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact (mul_le_mul' le_rfl ih).trans (hE.rad_mul.trans hE.rad_le)

theorem LocalCorner.mul_pow_mul_le (hE : LocalCorner E εE NE a loE) (i : ℕ) :
    E 0 * (NE ^ i * E 0) ≤ NE ^ i * E 0 := by
  cases i with
  | zero =>
    rw [pow_zero, one_mul]
    simpa using hE.mul_le 0 0
  | succ i =>
    calc E 0 * (NE ^ (i + 1) * E 0) = E 0 * NE * (NE ^ i * E 0) := by
          rw [pow_succ', mul_assoc NE, mul_assoc]
      _ ≤ NE * (NE ^ i * E 0) := mul_le_mul' hE.mul_rad le_rfl
      _ = NE ^ (i + 1) * E 0 := by rw [pow_succ', mul_assoc]

theorem LocalCorner.pow_mul_eq_bot (hE : LocalCorner E εE NE a loE) {i : ℕ} (hi : a ≤ i) :
    NE ^ i * E 0 = ⊥ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [pow_add, hE.rad_pow, Submodule.bot_mul, Submodule.bot_mul]

/-- Every degree-zero element of a local corner is a scalar multiple of the identity plus a
nilpotent. -/
theorem LocalCorner.exists_isNilpotent_sub_smul (hE : LocalCorner E εE NE a loE) {z : R}
    (hz : z ∈ E 0) : ∃ c : k, IsNilpotent (z - c • εE) := by
  obtain ⟨c, hc⟩ := hE.residue z hz
  refine ⟨c, a, ?_⟩
  have h := Submodule.pow_mem_pow NE hc a
  rwa [hE.rad_pow, Submodule.mem_bot] at h

/-! ### The walk through products -/

/-- Products `x y` with `x ∈ E γ`, `y ∈ F (-γ)` (and `1` in degree zero). -/
def pairSet (E F : Deg → Submodule k R) (γ : Deg) : Set R :=
  {r | (∃ x ∈ E γ, ∃ y ∈ F (-γ), r = x * y) ∨ (γ = 0 ∧ r = 1)}

/-- Degree-zero products with a radical factor. -/
def radSet (E F : Deg → Submodule k R) (NE NF : Submodule k R) : Set R :=
  {r | ∃ x ∈ E 0, ∃ y ∈ F 0, (x ∈ NE ∨ y ∈ NF) ∧ r = x * y}

/-- Products `x y` of total degree zero with a nonzero `E`-degree or a radical factor. -/
def smallSet (E F : Deg → Submodule k R) (NE NF : Submodule k R) : Set R :=
  {r | ∃ γ : Deg, ∃ x ∈ E γ, ∃ y ∈ F (-γ), (γ ≠ 0 ∨ x ∈ NE ∨ y ∈ NF) ∧ r = x * y}

/-- Products of `radSet` elements, normalized: `εE εF r₁ ⋯ r_l = X Y` with `X` in the
`i`-th power of the radical of `E` and `Y` in the `j`-th of `F`, `l ≤ i + j`. -/
theorem radSet_prod_aux (hE : LocalCorner E εE NE a loE) (hF : LocalCorner F εF NF b loF)
    (hc : SuperComm E F) :
    ∀ l : List R, (∀ r ∈ l, r ∈ radSet E F NE NF) → ∃ i j : ℕ, l.length ≤ i + j ∧
      ∃ X ∈ NE ^ i * E 0, ∃ Y ∈ NF ^ j * F 0, εE * εF * l.prod = X * Y
  | [], _ => ⟨0, 0, le_rfl, εE, by simpa using hE.unit_mem, εF, by simpa using hF.unit_mem,
      by simp⟩
  | r :: l, hl => by
    obtain ⟨i, j, hij, X, hX, Y, hY, he⟩ := radSet_prod_aux hE hF hc l (fun s hs =>
      hl s (List.mem_cons_of_mem r hs))
    obtain ⟨x, hx0, y, hy0, hxy, rfl⟩ := hl r List.mem_cons_self
    have hX0 : X ∈ E 0 := hE.pow_mul_le i hX
    have hlead : εE * εF * (x * y) = x * y := calc
      εE * εF * (x * y) = εE * (εF * x) * y := by simp only [mul_assoc]
      _ = (εE * x) * (εF * y) := by rw [hc.zero_left hx0 hF.unit_mem]; simp only [mul_assoc]
      _ = x * y := by rw [hE.unit_mul 0 x hx0, hF.unit_mul 0 y hy0]
    have htail : x * y * (εE * εF) = x * y := calc
      x * y * (εE * εF) = x * (y * εE) * εF := by simp only [mul_assoc]
      _ = (x * εE) * (y * εF) := by rw [hc.zero_left hE.unit_mem hy0]; simp only [mul_assoc]
      _ = x * y := by rw [hE.mul_unit 0 x hx0, hF.mul_unit 0 y hy0]
    have hprod : εE * εF * (x * y * l.prod) = x * X * (y * Y) := calc
      εE * εF * (x * y * l.prod) = x * y * (εE * εF * l.prod) := by
        rw [← mul_assoc, hlead, ← mul_assoc (x * y), htail]
      _ = x * (y * X) * Y := by rw [he]; simp only [mul_assoc]
      _ = x * X * (y * Y) := by rw [hc.zero_right hX0 hy0]; simp only [mul_assoc]
    rcases hxy with hxN | hyN
    · refine ⟨i + 1, j, by simp; omega, x * X, ?_, y * Y, ?_, by simpa using hprod⟩
      · rw [pow_succ', mul_assoc]; exact Submodule.mul_mem_mul hxN hX
      · exact hF.mul_pow_mul_le j (Submodule.mul_mem_mul hy0 hY)
    · refine ⟨i, j + 1, by simp; omega, x * X, ?_, y * Y, ?_, by simpa using hprod⟩
      · exact hE.mul_pow_mul_le i (Submodule.mul_mem_mul hx0 hX)
      · rw [pow_succ', mul_assoc]; exact Submodule.mul_mem_mul hyN hY

/-- Products of `a + b + 1` elements of `radSet` vanish. -/
theorem radSet_prod (hE : LocalCorner E εE NE a loE) (hF : LocalCorner F εF NF b loF)
    (hc : SuperComm E F) (l : List R) (hlen : l.length = a + b + 1)
    (hl : ∀ r ∈ l, r ∈ radSet E F NE NF) : l.prod = 0 := by
  obtain ⟨i, j, hij, X, hX, Y, hY, he⟩ := radSet_prod_aux hE hF hc l hl
  have hlead : εE * εF * l.prod = l.prod := by
    obtain ⟨r, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain ⟨x, hx0, y, hy0, -, rfl⟩ := hl r List.mem_cons_self
    calc εE * εF * (x * y :: l').prod = εE * (εF * x) * y * l'.prod := by
          simp only [List.prod_cons, mul_assoc]
      _ = (εE * x) * (εF * y) * l'.prod := by
          rw [hc.zero_left hx0 hF.unit_mem]; simp only [mul_assoc]
      _ = (x * y :: l').prod := by
          rw [hE.unit_mul 0 x hx0, hF.unit_mul 0 y hy0, List.prod_cons, mul_assoc]
  rw [← hlead, he]
  rcases le_or_gt a i with hi | hi
  · rw [hE.pow_mul_eq_bot hi, Submodule.mem_bot] at hX
    rw [hX, zero_mul]
  · rw [hF.pow_mul_eq_bot (show b ≤ j by omega), Submodule.mem_bot] at hY
    rw [hY, mul_zero]

theorem walk_pairSet (hE : LocalCorner E εE NE a loE) (hF : LocalCorner F εF NF b loF)
    (hc : SuperComm E F) :
    Walk (pairSet E F) (radSet E F NE NF) ((Icc (-(loE : ℤ)) loF) ×ˢ univ) (a + b + 1) where
  one_mem := Or.inr ⟨rfl, rfl⟩
  mul_mem := by
    intro γ δ r s hr hs
    rcases hr with ⟨x, hx, y, hy, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hs with ⟨x', hx', y', hy', rfl⟩ | ⟨rfl, rfl⟩
      · have hyy : y * y' ∈ F (-(γ + δ)) := by rw [neg_add]; exact hF.mul_mem hy hy'
        rw [hc.mul_pair hx' hy]
        exact Or.inl ⟨_, zsmul_mem (hE.mul_mem hx hx') _, _, hyy, rfl⟩
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
      obtain ⟨x, hx0, y, hy0, hxy, rfl⟩ := hr
      have e : x * y * (x' * y') = x * x' * (y * y') := by
        rw [mul_assoc, ← mul_assoc y, hc.zero_right hx' hy0]; simp only [mul_assoc]
      refine ⟨x * x', by simpa using hE.mul_mem hx0 hx', y * y',
        by simpa using hF.mul_mem hy0 hy', ?_, e⟩
      rcases hxy with hxN | hyN
      · exact Or.inl (hE.rad_mul (Submodule.mul_mem_mul hxN hx'))
      · exact Or.inr (hF.rad_mul (Submodule.mul_mem_mul hyN hy'))
    · rw [mul_one]; exact hr
  pair_mem_N := by
    intro γ r s hγ hr hs
    rcases hr with ⟨x, hx, y, hy, rfl⟩ | ⟨h, -⟩
    · rcases hs with ⟨x', hx', y', hy', rfl⟩ | ⟨h, -⟩
      · rw [neg_neg] at hy'
        have hxx := zsmul_mem (hE.pair_le γ hγ (Submodule.mul_mem_mul hx hx'))
          (ksign (-γ).2 (-γ).2)
        rw [hc.mul_pair hx' hy]
        exact ⟨_, hE.rad_le hxx, _, by simpa using hF.mul_mem hy hy', Or.inl hxx, rfl⟩
      · exact absurd (neg_eq_zero.mp h) hγ
    · exact absurd h hγ
  nil := radSet_prod hE hF hc

theorem smallSet_spec {r : R} (hr : r ∈ smallSet E F NE NF) :
    ∃ γ : Deg, r ∈ pairSet E F γ ∧ (γ ≠ 0 ∨ r ∈ radSet E F NE NF) := by
  obtain ⟨γ, x, hx, y, hy, h, rfl⟩ := hr
  by_cases hγ : γ = 0
  · subst hγ
    rw [neg_zero] at hy
    exact ⟨0, Or.inl ⟨x, hx, y, by simpa using hy, rfl⟩,
      Or.inr ⟨x, hx, y, hy, h.resolve_left (by simp), rfl⟩⟩
  · exact ⟨γ, Or.inl ⟨x, hx, y, hy, rfl⟩, Or.inl hγ⟩

/-- Long products of elements of `smallSet` vanish. -/
theorem smallSet_pow (hE : LocalCorner E εE NE a loE) (hF : LocalCorner F εF NF b loF)
    (hc : SuperComm E F) {L : ℕ} (hL : (loE + loF + 1) * 2 * (a + b + 1) < L + 1) {r : R}
    (hr : r ∈ smallSet E F NE NF ^ L) : r = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hr
  choose γ hγ using fun i : Fin L => smallSet_spec (f i).2
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
  · have hcard : #((Icc (-(loE : ℤ)) loF) ×ˢ (univ : Finset (ZMod 2))) =
        (loE + loF + 1) * 2 := by
      rw [card_product, Int.card_Icc]
      simp only [card_univ, ZMod.card]
      omega
    rw [hcard]; exact hL

/-! ### The product family -/

/-- Generators of the products of total degree `γ`. -/
def genSet (E F : Deg → Submodule k R) (γ : Deg) : Set R :=
  {r | ∃ δ : Deg, ∃ x ∈ E δ, ∃ y ∈ F (γ - δ), r = x * y}

/-- The products `E δ * F (γ - δ)` of total degree `γ`. -/
def prodFam (E F : Deg → Submodule k R) (γ : Deg) : Submodule k R :=
  Submodule.span k (genSet E F γ)

/-- A product of a degree-zero product with a small one is small. -/
theorem small_mul_mem (hE : LocalCorner E εE NE a loE) (hF : LocalCorner F εF NF b loF)
    (hc : SuperComm E F) {γ γ' : Deg} {x y x' y' : R} (hx : x ∈ E γ) (hy : y ∈ F (-γ))
    (hx' : x' ∈ E γ') (hy' : y' ∈ F (-γ'))
    (h : (γ ≠ 0 ∨ x ∈ NE ∨ y ∈ NF) ∨ (γ' ≠ 0 ∨ x' ∈ NE ∨ y' ∈ NF)) :
    x * y * (x' * y') ∈ smallSet E F NE NF := by
  rw [hc.mul_pair hx' hy]
  set s := ksign γ'.2 (-γ).2
  have hyy : y * y' ∈ F (-(γ + γ')) := by rw [neg_add]; exact hF.mul_mem hy hy'
  refine ⟨γ + γ', _, zsmul_mem (hE.mul_mem hx hx') s, _, hyy, ?_, rfl⟩
  by_cases h0 : γ + γ' = 0
  · right
    have hγ' : γ' = -γ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
    subst hγ'
    by_cases hγ : γ = 0
    · subst hγ
      simp only [neg_zero, ne_eq, not_true_eq_false, false_or] at h hy hy' hx'
      rcases h with (hN | hN) | (hN | hN)
      · exact Or.inl (zsmul_mem (hE.rad_mul (Submodule.mul_mem_mul hN hx')) s)
      · exact Or.inr (hF.rad_mul (Submodule.mul_mem_mul hN hy'))
      · exact Or.inl (zsmul_mem (hE.mul_rad (Submodule.mul_mem_mul hx hN)) s)
      · exact Or.inr (hF.mul_rad (Submodule.mul_mem_mul hy hN))
    · exact Or.inl (zsmul_mem (hE.pair_le γ hγ (Submodule.mul_mem_mul hx hx')) s)
  · exact Or.inl h0

/-- **Products of supercommuting local corners are local corners.** -/
theorem LocalCorner.mul (hE : LocalCorner E εE NE a loE) (hF : LocalCorner F εF NF b loF)
    (hc : SuperComm E F) :
    LocalCorner (prodFam E F) (εE * εF) (Submodule.span k (smallSet E F NE NF))
      ((loE + loF + 1) * 2 * (a + b + 1)) (loE + loF) where
  mul_le γ δ := by
    rw [prodFam, prodFam, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨δ₁, x, hx, y, hy, rfl⟩, _, ⟨δ₂, x', hx', y', hy', rfl⟩, rfl⟩
    show x * y * (x' * y') ∈ _
    rw [hc.mul_pair hx' hy]
    refine Submodule.subset_span ⟨δ₁ + δ₂, _, zsmul_mem (hE.mul_mem hx hx') _, _, ?_, rfl⟩
    have h := hF.mul_mem hy hy'
    convert h using 2
    abel
  unit_mem := Submodule.subset_span ⟨0, εE, hE.unit_mem, εF, by simpa using hF.unit_mem, rfl⟩
  unit_mul γ z hz := by
    induction hz using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨δ, x, hx, y, hy, rfl⟩ := hr
      calc εE * εF * (x * y) = εE * (εF * x) * y := by simp only [mul_assoc]
        _ = (εE * x) * (εF * y) := by rw [hc.zero_right hx hF.unit_mem]; simp only [mul_assoc]
        _ = x * y := by rw [hE.unit_mul δ x hx, hF.unit_mul _ y hy]
    | zero => rw [mul_zero]
    | add z w _ _ hz hw => rw [mul_add, hz, hw]
    | smul c z _ hz => rw [mul_smul_comm, hz]
  mul_unit γ z hz := by
    induction hz using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨δ, x, hx, y, hy, rfl⟩ := hr
      calc x * y * (εE * εF) = x * (y * εE) * εF := by simp only [mul_assoc]
        _ = (x * εE) * (y * εF) := by rw [hc.zero_left hE.unit_mem hy]; simp only [mul_assoc]
        _ = x * y := by rw [hE.mul_unit δ x hx, hF.mul_unit _ y hy]
    | zero => rw [zero_mul]
    | add z w _ _ hz hw => rw [add_mul, hz, hw]
    | smul c z _ hz => rw [smul_mul_assoc, hz]
  rad_le := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, hx, y, hy, -, rfl⟩
    exact Submodule.subset_span ⟨γ, x, hx, y, by rwa [zero_sub], rfl⟩
  mul_rad := by
    rw [prodFam, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨δ, x, hx, y, hy, rfl⟩, _, ⟨γ', x', hx', y', hy', hs, rfl⟩, rfl⟩
    rw [zero_sub] at hy
    exact Submodule.subset_span (small_mul_mem hE hF hc hx hy hx' hy' (Or.inr hs))
  rad_mul := by
    rw [prodFam, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨γ', x', hx', y', hy', hs, rfl⟩, _, ⟨δ, x, hx, y, hy, rfl⟩, rfl⟩
    rw [zero_sub] at hy
    exact Submodule.subset_span (small_mul_mem hE hF hc hx' hy' hx hy (Or.inl hs))
  rad_pow := by
    rw [Submodule.span_pow]
    exact Submodule.span_eq_bot.mpr fun r hr => smallSet_pow hE hF hc (Nat.lt_succ_self _) hr
  residue z hz := by
    induction hz using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨δ, x, hx, y, hy, rfl⟩ := hr
      rw [zero_sub] at hy
      by_cases hδ : δ = 0
      · subst hδ
        rw [neg_zero] at hy
        obtain ⟨c, hc⟩ := hE.residue x hx
        obtain ⟨c', hc'⟩ := hF.residue y hy
        refine ⟨c * c', ?_⟩
        set n := x - c • εE
        set n' := y - c' • εF
        have e : x * y - (c * c') • (εE * εF) = c • (εE * n') + n * y := by
          have hx' : x = c • εE + n := by simp [n]
          have hy' : y = c' • εF + n' := by simp [n']
          calc x * y - (c * c') • (εE * εF) = (c • εE + n) * y - (c * c') • (εE * εF) := by
                rw [← hx']
            _ = c • (εE * (c' • εF + n')) + n * y - (c * c') • (εE * εF) := by
                rw [add_mul, smul_mul_assoc, ← hy']
            _ = _ := by
                rw [mul_add, mul_smul_comm, smul_add, smul_smul]; abel
        rw [e]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
          (Submodule.subset_span ?_)
        · exact ⟨0, εE, hE.unit_mem, n', by simpa using hF.rad_le hc', Or.inr (Or.inr hc'),
            rfl⟩
        · exact ⟨0, n, hE.rad_le hc, y, by simpa using hy, Or.inr (Or.inl hc), rfl⟩
      · exact ⟨0, by
          rw [zero_smul, sub_zero]
          exact Submodule.subset_span ⟨δ, x, hx, y, hy, Or.inl hδ, rfl⟩⟩
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨c, hc⟩ := hz
      obtain ⟨c', hc'⟩ := hw
      refine ⟨c + c', ?_⟩
      rw [add_smul, add_sub_add_comm]
      exact Submodule.add_mem _ hc hc'
    | smul d z _ hz =>
      obtain ⟨c, hc⟩ := hz
      refine ⟨d * c, ?_⟩
      rw [mul_smul, ← smul_sub]
      exact Submodule.smul_mem _ d hc
  pair_le γ hγ := by
    rw [prodFam, prodFam, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨δ₁, x, hx, y, hy, rfl⟩, _, ⟨δ₂, x', hx', y', hy', rfl⟩, rfl⟩
    show x * y * (x' * y') ∈ _
    rw [hc.mul_pair hx' hy]
    set s := ksign δ₂.2 (γ - δ₁).2
    have hyy : y * y' ∈ F (-(δ₁ + δ₂)) := by
      have h := hF.mul_mem hy hy'
      convert h using 2
      abel
    refine Submodule.subset_span ⟨δ₁ + δ₂, _, zsmul_mem (hE.mul_mem hx hx') s, _, hyy, ?_, rfl⟩
    by_cases h0 : δ₁ + δ₂ = 0
    · right
      have hδ₂ : δ₂ = -δ₁ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
      subst hδ₂
      by_cases hδ₁ : δ₁ = 0
      · subst hδ₁
        right
        simp only [neg_zero, sub_zero] at hy hy'
        exact hF.pair_le γ hγ (Submodule.mul_mem_mul hy hy')
      · exact Or.inl (zsmul_mem (hE.pair_le δ₁ hδ₁ (Submodule.mul_mem_mul hx hx')) s)
    · exact Or.inl h0
  eq_bot γ hγ := by
    rw [prodFam, Submodule.span_eq_bot]
    rintro _ ⟨δ, x, hx, y, hy, rfl⟩
    by_cases hδ : δ.1 < -(loE : ℤ)
    · rw [hE.eq_bot δ hδ, Submodule.mem_bot] at hx; rw [hx, zero_mul]
    · have h : (γ - δ).1 < -(loF : ℤ) := by
        rw [Prod.fst_sub]; push_cast at hγ; omega
      rw [hF.eq_bot _ h, Submodule.mem_bot] at hy; rw [hy, mul_zero]

/-- A family supercommuting with `E` and `F` supercommutes with `prodFam E F`. -/
theorem SuperComm.prodFam (hEG : SuperComm E G) (hFG : SuperComm F G) :
    SuperComm (prodFam E F) G := by
  intro γ δ z y hz hy
  induction hz using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨δ₁, x₁, hx₁, x₂, hx₂, rfl⟩ := hr
    exact SuperComm.prodFam_aux hEG hFG hx₁ hx₂ hy
  | zero => simp
  | add z w _ _ hz hw => rw [mul_add, hz, hw, add_mul, smul_add]
  | smul c z _ hz => rw [mul_smul_comm, hz, smul_mul_assoc, smul_comm]

end OddMath.SKM.GradedWalk

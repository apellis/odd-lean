/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LieLean.RepresentationTheory.Crystal.Basic

/-!
# Super Cartan data and root data for covering quantum groups

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2 ([BE2]), §9 (first paragraph):
the Cartan matrix is symmetrized by positive integers `(dᵢ)_{i ∈ I}`, the parity of `I` satisfies
(1.4) (`dᵢⱼ = -aᵢⱼ` is even when `i` is odd), and `(-,-)` is the symmetric bilinear form on the
root lattice with `(αᵢ, αⱼ) = -dᵢ dᵢⱼ = dᵢ aᵢⱼ`.

Clark–Hill–Wang, *Quantum supergroups I*, arXiv:1301.1665v2 ([CHW1]), §1.1, define a super Cartan
datum as a symmetric bilinear form `ν, ν' ↦ ν · ν'` on `ℤ[I]` with (a) `dᵢ = i·i/2 ∈ ℤ_{>0}`,
(b) `2 i·j/i·i ∈ -ℕ` for `i ≠ j`, together with a decomposition `I = I₀ ⊔ I₁` with (c) `I₁ ≠ ∅`
and (d) `2 i·j/i·i ∈ 2ℤ` for `i ∈ I₁`; it is *bar-consistent* if (e) `dᵢ ≡ p(i) mod 2`.
The two formulations agree with `i · j = dᵢ aᵢⱼ` (`SuperCartanDatum.dot`); see
`SuperCartanDatum.two_mul_dot_div` and `SuperCartanDatum.dot_self`.

We follow [BE2]: `I` is not assumed finite and `I₁` may be empty (condition (c) of [CHW1] is
dropped; for `I₁ = ∅` one recovers the ordinary quantum group). Bar-consistency
([BE2] (10.2), [CHW1] §1.1 (e), Clark arXiv:1312.4855v2 Def. 2.1(d)) is a separate predicate,
`SuperCartanDatum.BarConsistent`, assumed only where needed.

A root datum (`RootDatum`) adds a weight lattice `X` with simple roots `αᵢ ∈ X` and coroots
`⟨hᵢ, -⟩ : X → ℤ` (lie-lean's `CartanDatum I X`) such that `⟨hᵢ, αⱼ⟩ = aᵢⱼ`. [BE2] takes the weight
lattice `P` of a realization; [CHW1] §1.2 takes a perfect pairing `Y × X → ℤ`. Neither linear
independence nor perfectness is needed for the definitions of `f` and `U̇_{q,π}(𝔤)`.

## Main definitions

* `SuperCartanDatum I`: a symmetrizable generalized Cartan matrix with positive integral
  symmetrizer and a parity satisfying [BE2] (1.4).
* `SuperCartanDatum.dot`: `i · j = dᵢ aᵢⱼ`; `SuperCartanDatum.wdot`: its extension to `ℕ[I]`.
* `SuperCartanDatum.BarConsistent`: [BE2] (10.2).
* `RootDatum I X`: a super Cartan datum with weights, roots and coroots.

## Main results

* `SuperCartanDatum.dot_comm`, `SuperCartanDatum.dot_self`, `SuperCartanDatum.two_mul_dot_div`,
  `SuperCartanDatum.dot_nonpos`: the axioms (a), (b) of [CHW1] §1.1.
* `SuperCartanDatum.even_dot_of_barConsistent`: (d) and (e) imply (f) `i · j ∈ 2ℤ` ([CHW1] §1.1).
-/

namespace OddMath.CoveringQuantum

/-- A super Cartan datum ([BE2] §1 and §9; [CHW1] §1.1): a generalized Cartan matrix `a`
symmetrized by positive integers `dᵢ` (`dᵢ aᵢⱼ = dⱼ aⱼᵢ`), and a parity `I → ℤ/2` such that
`aᵢⱼ` is even whenever `i` is odd ([BE2] (1.4), [CHW1] §1.1 (d)). -/
structure SuperCartanDatum (I : Type*) where
  /-- The generalized Cartan matrix `aᵢⱼ = ⟨hᵢ, αⱼ⟩ = -dᵢⱼ`. -/
  a : Matrix I I ℤ
  isGCM : a.IsGeneralizedCartan
  /-- The symmetrizer. -/
  d : I → ℕ
  d_pos : ∀ i, 0 < d i
  d_mul_symm : ∀ i j, (d i : ℤ) * a i j = d j * a j i
  /-- The parity `i ↦ |i|`. -/
  parity : I → ZMod 2
  /-- [BE2] (1.4): `aᵢⱼ` is even if `i` is odd. -/
  even_of_odd : ∀ i j, parity i = 1 → Even (a i j)

namespace SuperCartanDatum

variable {I : Type*} (C : SuperCartanDatum I)

/-- The symmetric bilinear form `i · j = (αᵢ, αⱼ) = dᵢ aᵢⱼ` on the root lattice. -/
def dot (i j : I) : ℤ := C.d i * C.a i j

theorem dot_comm (i j : I) : C.dot i j = C.dot j i := C.d_mul_symm i j

/-- [CHW1] §1.1 (a): `i · i = 2 dᵢ`. -/
theorem dot_self (i : I) : C.dot i i = 2 * C.d i := by
  simp [dot, C.isGCM.diag i, mul_comm]

theorem dot_self_pos (i : I) : 0 < C.dot i i := by
  rw [dot_self]; have := C.d_pos i; omega

/-- [CHW1] §1.1 (b), first half: `2 (i · j) / (i · i) = aᵢⱼ`. -/
theorem two_mul_dot_div (i j : I) : 2 * C.dot i j / C.dot i i = C.a i j := by
  rw [dot_self, dot, ← mul_assoc, mul_comm (2 : ℤ), mul_comm _ (C.a i j), Int.mul_ediv_cancel]
  have := C.d_pos i; omega

/-- [CHW1] §1.1 (b), second half: `i · j ≤ 0` for `i ≠ j`. -/
theorem dot_nonpos {i j : I} (h : i ≠ j) : C.dot i j ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) (C.isGCM.offDiag_nonpos i j h)

/-- For odd `i`, `aᵢⱼ` is even ([CHW1] §1.1 (d)), hence so is `i · j = dᵢ aᵢⱼ`. -/
theorem even_dot_of_odd {i : I} (hi : C.parity i = 1) (j : I) : Even (C.dot i j) :=
  (C.even_of_odd i j hi).mul_left _

/-- The form `ν · μ = Σᵢⱼ νᵢ μⱼ (i · j)` on `ℕ[I]`, modelled as `I →₀ ℕ`. -/
def wdot (ν μ : I →₀ ℕ) : ℤ := ν.sum fun i m ↦ μ.sum fun j n ↦ (m * n : ℤ) * C.dot i j

theorem wdot_comm (ν μ : I →₀ ℕ) : C.wdot ν μ = C.wdot μ ν := by
  simp only [wdot]
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun i _ ↦ Finsupp.sum_congr fun j _ ↦ ?_
  rw [C.dot_comm]; ring

/-- The parity `p(ν) = Σᵢ νᵢ |i|` of `ν ∈ ℕ[I]`. -/
def wpar (ν : I →₀ ℕ) : ZMod 2 := ν.sum fun i m ↦ (m : ZMod 2) * C.parity i

theorem wpar_add (ν μ : I →₀ ℕ) : C.wpar (ν + μ) = C.wpar ν + C.wpar μ := by
  simp only [wpar]
  exact Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ by push_cast; ring)

@[simp] theorem wpar_single (i : I) (m : ℕ) : C.wpar (Finsupp.single i m) = m * C.parity i := by
  simp [wpar]

@[simp] theorem wpar_zero : C.wpar 0 = 0 := by simp [wpar]

/-- Bar-consistency ([BE2] (10.2); [CHW1] §1.1 (e); Clark, arXiv:1312.4855v2, Def. 2.1 (d)):
`dᵢ ≡ |i| (mod 2)` for every `i`. -/
def BarConsistent : Prop := ∀ i, (C.d i : ZMod 2) = C.parity i

/-- [CHW1] §1.1 (f): for a bar-consistent datum, `i · j ∈ 2ℤ` for all `i, j`. -/
theorem even_dot_of_barConsistent (hC : C.BarConsistent) (i j : I) : Even (C.dot i j) := by
  by_cases hi : C.parity i = 1
  · exact C.even_dot_of_odd hi j
  · have h0 : C.parity i = 0 := by
      have := hC i
      generalize C.parity i = p at hi ⊢
      fin_cases p <;> simp_all
    have : (C.d i : ZMod 2) = 0 := by rw [hC i, h0]
    rw [ZMod.natCast_eq_zero_iff_even] at this
    exact (this.natCast (α := ℤ)).mul_right _

end SuperCartanDatum

/-- A root datum for a super Cartan datum ([BE2] §1 and §9; cf. [CHW1] §1.2): a weight lattice
`X` with simple roots `αᵢ` and coroots `⟨hᵢ, -⟩` (lie-lean's `CartanDatum I X`) such that
`⟨hᵢ, αⱼ⟩ = aᵢⱼ`. -/
structure RootDatum (I X : Type*) [AddCommGroup X] extends SuperCartanDatum I where
  /-- Simple roots and coroots. -/
  cd : CartanDatum I X
  coroot_root : ∀ i j, cd.coroot i (cd.root j) = a i j

namespace RootDatum

variable {I X : Type*} [AddCommGroup X] (D : RootDatum I X)

/-- The simple root `αᵢ`. -/
abbrev α (i : I) : X := D.cd.root i

/-- `⟨hᵢ, λ⟩`. -/
abbrev h (i : I) (μ : X) : ℤ := D.cd.coroot i μ

theorem h_α (i j : I) : D.h i (D.α j) = D.a i j := D.coroot_root i j

/-- The integer `|i, λ| = |i| (⟨hᵢ, λ⟩ + 1)` of [BE2] (1.15), as an element of `ℤ/2`. -/
def parl (i : I) (μ : X) : ZMod 2 := D.parity i * ((D.h i μ : ZMod 2) + 1)

/-- `|i, λ|` depends on `λ` only through `⟨hᵢ, λ⟩ mod 2`; for odd `i` it is unchanged by adding
roots ([BE2] (1.4)). -/
theorem parl_add_α (i j : I) (μ : X) : D.parl i (μ + D.α j) = D.parl i μ := by
  simp only [parl, map_add, h_α]
  by_cases hi : D.parity i = 1
  · obtain ⟨m, hm⟩ := D.even_of_odd i j hi
    rw [hm]; push_cast
    have h2 : ((m : ZMod 2) + m) = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
    linear_combination D.parity i * h2
  · have h0 : D.parity i = 0 := by
      generalize D.parity i = p at hi ⊢
      fin_cases p <;> simp_all
    simp [h0]

end RootDatum

end OddMath.CoveringQuantum

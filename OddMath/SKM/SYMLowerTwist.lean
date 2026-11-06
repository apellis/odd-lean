/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.TwistedClosureDetector
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Lowering twists of the bubble coefficient algebra

For Brundan–Wang–Webster parameters (arXiv:2505.22929v2, §2.2), sliding a bubble across a
strand of another colour (Brundan–Ellis, arXiv:1701.04133v2, Proposition 7.3(iii),
(7.11)–(7.12)) changes the zero-dot coefficient: the pure monomials `cᵢⱼ(r, 0) u^r`,
`r < dᵢⱼ`, of `Qᵢⱼ(u, v)` add bubbles of strictly smaller degree. On the coefficient algebra
`SYM D k` of (1.21) this is the algebra endomorphism `lowerTwist a` sending the elementary
generator `e_m` of colour `i` to `e_m + Σ_{0 < s ≤ m} a i s • e_{m-s}` (with `e_0 = 1`) and
fixing the odd generators.

* `SYM.lowerTwist`: the twist, for an arbitrary coefficient family `a`.
* `SYM.degLE`: the span of the monomials of degree at most `n`, where `e i n` has degree
  `n + 1` and an odd generator degree `1`.
* `SYM.lowerTwist_bijective`: every lowering twist is bijective. The twist is the identity
  plus a map lowering the exhaustive filtration `degLE`
  (`OrientedReduction.bijective_id_add_of_lowering`).
-/

noncomputable section

universe u v w

namespace OddMath.SKM
open Finset

namespace SYM

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (k : Type w) [CommRing k]

/-- The elementary generator `e_m` of colour `i` with `e_0 = 1`: `eUp i 0 = 1` and
`eUp i (n + 1) = e i n`. -/
def eUp (i : I) : ℕ → SYM D k
  | 0 => 1
  | n + 1 => e D k i n

theorem eUp_commute (i j : I) (m n : ℕ) : Commute (eUp D k i m) (eUp D k j n) := by
  cases m <;> cases n
  · exact Commute.one_left _
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact e_commute D k _ _ _ _

theorem eUp_delta_commute (i : I) (m : ℕ) (j : {j : I // D.parity j = 1}) :
    Commute (eUp D k i m) (delta D k j) := by
  cases m
  · exact Commute.one_left _
  · exact e_delta_commute D k _ _ _

/-- The lowered image of `e_m` of colour `i`: `e_m + Σ_{0 < s ≤ m} a i s • e_{m-s}`. -/
def lowerE (a : I → ℕ → k) (i : I) (m : ℕ) : SYM D k :=
  eUp D k i m + ∑ s ∈ Ioc 0 m, a i s • eUp D k i (m - s)

theorem lowerE_commute (a : I → ℕ → k) (i j : I) (m n : ℕ) :
    Commute (lowerE D k a i m) (lowerE D k a j n) := by
  unfold lowerE
  refine Commute.add_left (Commute.add_right (eUp_commute D k _ _ _ _) ?_) ?_
  · exact Commute.sum_right _ _ _ fun s _ =>
      Commute.smul_right (eUp_commute D k _ _ _ _) _
  · refine Commute.sum_left _ _ _ fun s _ => Commute.smul_left ?_ _
    refine Commute.add_right (eUp_commute D k _ _ _ _) ?_
    exact Commute.sum_right _ _ _ fun t _ => Commute.smul_right (eUp_commute D k _ _ _ _) _

theorem lowerE_delta_commute (a : I → ℕ → k) (i : I) (m : ℕ)
    (j : {j : I // D.parity j = 1}) : Commute (lowerE D k a i m) (delta D k j) := by
  unfold lowerE
  refine Commute.add_left (eUp_delta_commute D k _ _ _) ?_
  exact Commute.sum_left _ _ _ fun s _ =>
    Commute.smul_left (eUp_delta_commute D k _ _ _) _

/-- Generator images of the lowering twist: `e i n ↦ lowerE a i (n + 1)`, odd generators
fixed. -/
def lowerGen (a : I → ℕ → k) : SYMGen D → SYM D k
  | .inl (i, n) => lowerE D k a i (n + 1)
  | .inr i => delta D k i

theorem lowerGen_rel (a : I → ℕ → k) ⦃x y : FreeAlgebra k (SYMGen D)⦄
    (h : SYMRel D k x y) :
    FreeAlgebra.lift k (lowerGen D k a) x = FreeAlgebra.lift k (lowerGen D k a) y := by
  cases h with
  | polynomial a' b' =>
    simp only [map_mul, FreeAlgebra.lift_ι_apply, lowerGen]
    exact lowerE_commute D k a _ _ _ _
  | mixed a' j =>
    simp only [map_mul, FreeAlgebra.lift_ι_apply, lowerGen]
    exact lowerE_delta_commute D k a _ _ _
  | exterior i j =>
    simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, lowerGen]
    exact delta_anticommute D k i j
  | square i =>
    simp only [map_pow, map_zero, FreeAlgebra.lift_ι_apply, lowerGen]
    exact delta_sq D k i

/-- The lowering twist of `SYM`: the algebra endomorphism sending `e_m` of colour `i` to
`e_m + Σ_{0 < s ≤ m} a i s • e_{m-s}` (with `e_0 = 1`) and fixing the odd generators. -/
def lowerTwist (a : I → ℕ → k) : SYM D k →ₐ[k] SYM D k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (lowerGen D k a), lowerGen_rel D k a⟩

@[simp] theorem lowerTwist_ι (a : I → ℕ → k) (g : SYMGen D) :
    lowerTwist D k a (ι D k g) = lowerGen D k a g := by
  simp only [lowerTwist, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

/-! ### The degree filtration -/

/-- The degree of a generator: `e i n` has degree `n + 1`, an odd generator degree `1`. -/
def genDeg : SYMGen D → ℕ
  | .inl (_, n) => n + 1
  | .inr _ => 1

theorem one_le_genDeg (g : SYMGen D) : 1 ≤ genDeg D g := by
  cases g with
  | inl a => exact Nat.succ_pos _
  | inr _ => exact le_rfl

/-- The span of the monomials of degree at most `n`. -/
def degLE (n : ℕ) : Submodule k (SYM D k) :=
  Submodule.span k {x | ∃ l : List (SYMGen D), (l.map (genDeg D)).sum ≤ n ∧
    x = (l.map (ι D k)).prod}

theorem degLE_mono {m n : ℕ} (h : m ≤ n) : degLE D k m ≤ degLE D k n :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩

theorem one_mem_degLE (n : ℕ) : (1 : SYM D k) ∈ degLE D k n :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem ι_mem_degLE (g : SYMGen D) : ι D k g ∈ degLE D k (genDeg D g) :=
  Submodule.subset_span ⟨[g], by simp, by simp⟩

theorem mul_mem_degLE {m n : ℕ} {x y : SYM D k} (hx : x ∈ degLE D k m)
    (hy : y ∈ degLE D k n) : x * y ∈ degLE D k (m + n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ l', ?_, ?_⟩
      · simp only [List.map_append, List.sum_append]; omega
      · simp [List.prod_append]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

theorem eUp_mem_degLE (i : I) (m : ℕ) : eUp D k i m ∈ degLE D k m := by
  cases m with
  | zero => exact one_mem_degLE D k 0
  | succ n => exact ι_mem_degLE D k (.inl (i, n))

theorem lowerGen_sub_mem (a : I → ℕ → k) (g : SYMGen D) :
    lowerGen D k a g - ι D k g ∈ degLE D k (genDeg D g - 1) := by
  cases g with
  | inl p =>
    obtain ⟨i, n⟩ := p
    have h : lowerGen D k a (.inl (i, n)) - ι D k (.inl (i, n)) =
        ∑ s ∈ Ioc 0 (n + 1), a i s • eUp D k i (n + 1 - s) := by
      simp only [lowerGen, lowerE]; rw [show eUp D k i (n + 1) = ι D k (.inl (i, n)) from rfl]
      abel
    rw [h]
    exact Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _
      (degLE_mono D k (by simp only [genDeg, mem_Ioc] at hs ⊢; omega) (eUp_mem_degLE D k i _))
  | inr i =>
    show delta D k i - ι D k (.inr i) ∈ _
    rw [show delta D k i = ι D k (.inr i) from rfl, sub_self]
    exact Submodule.zero_mem _

theorem lowerGen_mem (a : I → ℕ → k) (g : SYMGen D) :
    lowerGen D k a g ∈ degLE D k (genDeg D g) := by
  have h := Submodule.add_mem _ (degLE_mono D k (Nat.sub_le _ 1) (lowerGen_sub_mem D k a g))
    (ι_mem_degLE D k g)
  rwa [sub_add_cancel] at h

/-- On a monomial of degree `w`, the twist is the monomial plus terms of degree `< w`. -/
theorem lowerTwist_prod_sub_mem (a : I → ℕ → k) :
    ∀ l : List (SYMGen D),
      lowerTwist D k a (l.map (ι D k)).prod - (l.map (ι D k)).prod ∈
        degLE D k ((l.map (genDeg D)).sum - 1) ∧
      lowerTwist D k a (l.map (ι D k)).prod ∈ degLE D k (l.map (genDeg D)).sum
  | [] => by simp [one_mem_degLE]
  | g :: l => by
    obtain ⟨ih₁, ih₂⟩ := lowerTwist_prod_sub_mem a l
    have hg := one_le_genDeg D g
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, lowerTwist_ι]
    refine ⟨?_, mul_mem_degLE D k (lowerGen_mem D k a g) ih₂⟩
    have E : lowerGen D k a g * lowerTwist D k a (l.map (ι D k)).prod -
        ι D k g * (l.map (ι D k)).prod =
        (lowerGen D k a g - ι D k g) * lowerTwist D k a (l.map (ι D k)).prod +
          ι D k g * (lowerTwist D k a (l.map (ι D k)).prod - (l.map (ι D k)).prod) := by
      rw [sub_mul, mul_sub]; abel
    rw [E]
    refine Submodule.add_mem _ ?_ ?_
    · exact degLE_mono D k (by omega) (mul_mem_degLE D k (lowerGen_sub_mem D k a g) ih₂)
    · rcases Nat.eq_zero_or_pos (l.map (genDeg D)).sum with h0 | h0
      · have : l = [] := by
          cases l with
          | nil => rfl
          | cons g' l' =>
            have := one_le_genDeg D g'
            simp only [List.map_cons, List.sum_cons] at h0; omega
        subst this
        simp
      · exact degLE_mono D k (by omega) (mul_mem_degLE D k (ι_mem_degLE D k g) ih₁)

theorem exists_mem_degLE (x : SYM D k) : ∃ n, x ∈ degLE D k n := by
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) x
  change ∃ n, mk D k p ∈ degLE D k n
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨0, ?_⟩
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_degLE D k 0)
  | grade1 g => exact ⟨_, ι_mem_degLE D k g⟩
  | mul p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨n, hn⟩ := hq
    exact ⟨m + n, by rw [map_mul]; exact mul_mem_degLE D k hm hn⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨n, hn⟩ := hq
    exact ⟨max m n, by
      rw [map_add]
      exact Submodule.add_mem _ (degLE_mono D k (le_max_left _ _) hm)
        (degLE_mono D k (le_max_right _ _) hn)⟩

/-- A lowering twist is bijective. -/
theorem lowerTwist_bijective (a : I → ℕ → k) : Function.Bijective (lowerTwist D k a) := by
  let N : SYM D k →ₗ[k] SYM D k := (lowerTwist D k a).toLinearMap - LinearMap.id
  have hN : LinearMap.id + N = (lowerTwist D k a).toLinearMap := by
    exact add_sub_cancel (LinearMap.id : SYM D k →ₗ[k] SYM D k) _
  have key : ∀ n, ∀ x ∈ degLE D k n, N x ∈ degLE D k (n - 1) := by
    intro n x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact degLE_mono D k (by omega) (lowerTwist_prod_sub_mem D k a l).1
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have h0 : ∀ x ∈ degLE D k 0, N x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have : l = [] := by
        cases l with
        | nil => rfl
        | cons g' l' =>
          have := one_le_genDeg D g'
          simp only [List.map_cons, List.sum_cons] at hl; omega
      subst this
      simp [N]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, hx, smul_zero]
  have H := OrientedReduction.bijective_id_add_of_lowering N (degLE D k)
    (exists_mem_degLE D k) h0 fun n x hx => key (n + 1) x hx
  rw [hN] at H
  exact H

end SYM
end OddMath.SKM

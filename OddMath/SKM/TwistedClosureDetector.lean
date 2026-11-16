/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PositiveClosureDetector
import Mathlib.Tactic.Abel

/-!
# Closure detection with a twisted principal coefficient

For Brundan–Ellis parameters (arXiv:1701.04133v2, (1.3)), the bubble slides of
Proposition 7.3(iii), (7.11)–(7.12) move a bubble across a strand of another colour with
unchanged zero-dot term: every other term has a dot on the strand. For the
Brundan–Wang–Webster parameters of arXiv:2505.22929v2, §2.2, the monomials `cᵢⱼ(r, 0) u^r`,
`r < dᵢⱼ`, of `Qᵢⱼ(u, v)` contribute zero-dot terms, namely bubbles of strictly smaller degree.
So the principal coefficient of a closure is no longer the input coefficient `p` but its
image `φ p` under a map that is the identity plus a strictly degree-lowering map.

This file records the two abstract facts that let the closure argument of the reduction of
Brundan–Ellis §8 (`OrientedReduction.injective_of_positive_closure`) absorb such a twist.

* `injective_of_positive_closure_twisted`: injectivity descends through a closure whose
  principal coefficient is `φ p` for an injective additive map `φ`.
* `bijective_id_add_of_lowering`: the identity plus a map lowering an exhaustive filtration
  is bijective. No monotonicity of the filtration is assumed.
-/

namespace OddMath.SKM.OrientedReduction
open scoped BigOperators

/-- Injectivity descends through a linear closure whose principal coefficient is twisted by an
injective additive map `φ`, with finite strictly positive-dot corrections. For `φ = id` this is
`injective_of_positive_closure`. -/
theorem injective_of_positive_closure_twisted
    {k R A M N : Type*} [CommRing k] [AddCommGroup R] [Module k R]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (dots : A → ℕ) (weak : (A →₀ R) →ₗ[k] M) (strong : (A →₀ R) →ₗ[k] N)
    (closure : M →ₗ[k] N) (hinj : Function.Injective strong)
    (φ : R →+ R) (hφ : Function.Injective φ)
    (h : ∀ i p, ∃ r : A →₀ R, (∀ j ∈ r.support, dots i < dots j) ∧
      closure (weak (Finsupp.single i p)) = strong (Finsupp.single i (φ p) + r)) :
    Function.Injective weak := by
  classical
  have hz : ∀ f, weak f = 0 → f = 0 := by
    intro f hf
    choose r hr he using fun i => h i (f i)
    let g : A →₀ R := Finsupp.mapRange φ φ.map_zero f
    have hg : g.support = f.support :=
      Finsupp.support_mapRange_of_injective φ.map_zero f hφ
    have H : strong (∑ i ∈ g.support, (Finsupp.single i (g i) + r i)) = 0 := by
      calc
        _ = ∑ i ∈ f.support, closure (weak (Finsupp.single i (f i))) := by
          rw [hg]
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [he i]
          rfl
        _ = closure (weak (∑ i ∈ f.support, Finsupp.single i (f i))) := by
          simp only [map_sum]
        _ = closure (weak f) := by
          change closure (weak (f.sum Finsupp.single)) = _
          rw [Finsupp.sum_single]
        _ = 0 := by rw [hf, map_zero]
    have H0 : (∑ i ∈ g.support, (Finsupp.single i (g i) + r i)) = 0 :=
      hinj (H.trans strong.map_zero.symm)
    have hg0 := eq_zero_of_positive_corrections dots g r hr H0
    ext i
    apply hφ
    have := congrArg (fun x : A →₀ R => x i) hg0
    simpa [g] using this
  intro f g hfg
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hfg, sub_self]

/-- The identity plus a map that lowers an exhaustive filtration is bijective: if
`N (F (n + 1)) ⊆ F n`, `N (F 0) = 0` and every vector lies in some `F n`, then `id + N` is
bijective. -/
theorem bijective_id_add_of_lowering {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (N : M →ₗ[k] M) (F : ℕ → Submodule k M) (hex : ∀ x, ∃ n, x ∈ F n)
    (h0 : ∀ x ∈ F 0, N x = 0) (hs : ∀ n, ∀ x ∈ F (n + 1), N x ∈ F n) :
    Function.Bijective (LinearMap.id (R := k) (M := M) + N) := by
  have hinj : ∀ n, ∀ x ∈ F n, x + N x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx he; rwa [h0 x hx, add_zero] at he
    | succ n ih =>
      intro x hx he
      have hx' : x = -N x := eq_neg_of_add_eq_zero_left he
      have hm : x ∈ F n := by rw [hx']; exact Submodule.neg_mem _ (hs n x hx)
      exact ih x hm he
  have hsurj : ∀ n, ∀ y ∈ F n, ∃ x, x + N x = y := by
    intro n
    induction n with
    | zero => intro y hy; exact ⟨y, by rw [h0 y hy, add_zero]⟩
    | succ n ih =>
      intro y hy
      obtain ⟨z, hz⟩ := ih (N y) (hs n y hy)
      exact ⟨y - z, by rw [map_sub]; rw [← hz]; abel⟩
  constructor
  · intro x y hxy
    simp only [LinearMap.add_apply, LinearMap.id_apply] at hxy
    apply sub_eq_zero.mp
    obtain ⟨n, hn⟩ := hex (x - y)
    apply hinj n _ hn
    rw [map_sub, show x - y + (N x - N y) = (x + N x) - (y + N y) by abel, hxy, sub_self]
  · intro y
    obtain ⟨n, hn⟩ := hex y
    obtain ⟨x, hx⟩ := hsurj n y hn
    exact ⟨x, by simpa using hx⟩

end OddMath.SKM.OrientedReduction

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# The reverse norm identity from injectivity of `G G'`

The ring-theoretic part of `docs/Nondegeneracy/DeformedBoundaryDivision.md` §§2–3, which
supplies the norm input `hz₀` of `MackeyBoundary.norm` (`BoundaryAssembly.lean`).

* `injective_of_leading` (§2): an additive map on finitely supported polynomials
  `ℕ →₀ V` in the moving variable that raises degrees by `d`, with injective top coefficient
  `v_N ↦ (f v)_(N+d)`, is injective. This is the step "the largest moving exponent of a
  finite nonzero vector cannot disappear" for right multiplication by `K = G G'` in the
  right-oriented PBW coordinates of `H e_R / J_R`.
* `mem_of_mul_mem_of_injective` (§2): if right multiplication by `G G'` is injective on
  `H / J_R` and `J_L G' ⊆ J_R`, then `h G ∈ J_L` implies `h ∈ J_R` (injectivity of `G`).
* `reverse_norm` (§3): from the all-prefix identity (3) `f T G ≡ f L_left (mod J_L)` and the
  transport identities (4) `G f = ε f' G`, `G L_left = L G`, the reverse norm identity (5)
  `G f T ≡ ε f' L (mod J_R)`.

The left ideals `J_L`, `J_R` are left `H`-submodules of `H`; no right action and no inverse of
a polynomial is used.
-/

namespace OddMath.QuiverHecke.CyclotomicAction.ReverseNorm

open Finsupp

section Leading

variable {V : Type*} [AddCommGroup V]

/-- **Leading-term injectivity.** If `f` sends a vector of moving degree `≤ N` to one of
degree `≤ N + d`, with top coefficient `c (v N)` for an injective `c`, then `f` is injective. -/
theorem injective_of_leading (f : (ℕ →₀ V) →+ (ℕ →₀ V)) (d : ℕ) (c : V →+ V)
    (hc : Function.Injective c)
    (hf : ∀ v N, (∀ l, N < l → v l = 0) →
      (∀ l, N + d < l → f v l = 0) ∧ f v (N + d) = c (v N)) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun v hv => ?_
  by_contra hne
  have hs : v.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  set N := v.support.max' hs
  have hN : ∀ l, N < l → v l = 0 := fun l hl => by
    by_contra h
    exact absurd (v.support.le_max' l (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hl)
  have htop : v N ≠ 0 := Finsupp.mem_support_iff.mp (v.support.max'_mem hs)
  have := (hf v N hN).2
  rw [hv, Finsupp.coe_zero, Pi.zero_apply] at this
  exact htop (hc (by rw [← this, map_zero]))

end Leading

section Ideals

variable {H : Type*} [Ring H]

/-- **Injectivity of `G`** (`DeformedBoundaryDivision.md` §2): if right multiplication by
`G G'` is injective modulo `J_R` and `J_L G' ⊆ J_R`, then `h G ∈ J_L` forces `h ∈ J_R`. -/
theorem mem_of_mul_mem_of_injective (JL JR : Submodule H H) {G G' : H}
    (hK : ∀ h, h * (G * G') ∈ JR → h ∈ JR) (hL' : ∀ h ∈ JL, h * G' ∈ JR) {h : H}
    (hG : h * G ∈ JL) : h ∈ JR :=
  hK h (by rw [← mul_assoc]; exact hL' _ hG)

/-- **The reverse norm identity (5)** (`DeformedBoundaryDivision.md` §3). From (3)
`f T G ≡ f L_left (mod J_L)` and (4) `G f = ε f' G`, `G L_left = L G`, the injectivity
hypotheses of `mem_of_mul_mem_of_injective` give `G f T ≡ ε f' L (mod J_R)`. -/
theorem reverse_norm (JL JR : Submodule H H) {G G' f f' T L Lleft ε : H}
    (hK : ∀ h, h * (G * G') ∈ JR → h ∈ JR) (hL' : ∀ h ∈ JL, h * G' ∈ JR)
    (h3 : f * T * G - f * Lleft ∈ JL) (h4f : G * f = ε * f' * G)
    (h4L : G * Lleft = L * G) :
    G * f * T - ε * f' * L ∈ JR := by
  refine mem_of_mul_mem_of_injective JL JR hK hL' ?_
  have : (G * f * T - ε * f' * L) * G = G * (f * T * G - f * Lleft) := by
    rw [sub_mul, mul_sub, mul_assoc (ε * f') L G, ← h4L, ← mul_assoc, ← h4f]
    simp only [mul_assoc]
  rw [this]
  exact JL.smul_mem G h3

end Ideals

end OddMath.QuiverHecke.CyclotomicAction.ReverseNorm

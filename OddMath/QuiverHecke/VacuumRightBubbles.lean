/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteNondegeneracy

/-! # The left-bubble series from the right-bubble moments

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8, in the scope of
`docs/Nondegeneracy/FieldScopeBoundary.md`.

At colours with `hᵢ(μ) ≤ 0` the dotted right bubbles are the ones computed directly at
the tensor vacuum: they are the cap moments of the chosen inverse column, whose
generating series is the moment series `(1-z)^(M_i)/E_i(-z)` at even colours and
`(1+z)^(M_i)/C_i(-z)` at odd colours
(`ELVOld.tensorVacuumNegativeCap_even_moments`, `tensorVacuumNegativeCap_odd_moments`).
This file shows that these right moments, together with the odd bubble, determine the
left bubbles: the infinite Grassmannian relations (5.5), (5.6) (`SKM.eq_5_5`,
`SKM.eq_5_6`) hold in every action, the right series has constant term one, and the
substituted series is its reciprocal (`VacuumSeries.substitutedSeries_mul_momentSeries`).
This is the converse direction of `AdjunctionBubbleSeries.right_even` and
`AdjunctionBubbleSeries.right_odd`.

* `VacuumRightBubblesNonpositiveHeight`: the right moments and the odd bubble at
  colours with `hᵢ(μ) ≤ 0`;
* `VacuumRightBubblesNonpositiveHeight.toNonpositiveHeight`: they give
  `VacuumBubblesNonpositiveHeight`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Finset
universe u w

/-- Two sequences `x, y` with `x₀ = y₀ = 1`, each a left inverse of the series `K` with
`K₀ = 1` (`Σ_(s ≤ n) x_s K_(n-s) = 0` for `n > 0`), are equal. -/
theorem eq_of_sum_mul_eq_zero_right {R : Type*} [Ring R] {x y K : ℕ → R} (hK : K 0 = 1)
    (hx0 : x 0 = 1) (hy0 : y 0 = 1)
    (hx : ∀ n, 0 < n → ∑ s ∈ range (n + 1), x s * K (n - s) = 0)
    (hy : ∀ n, 0 < n → ∑ s ∈ range (n + 1), y s * K (n - s) = 0) (n : ℕ) : x n = y n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases n with _ | n
    · rw [hx0, hy0]
    · have h1 := hx (n + 1) n.succ_pos
      have h2 := hy (n + 1) n.succ_pos
      rw [sum_range_succ, Nat.sub_self, hK, mul_one] at h1 h2
      have hsum : ∑ s ∈ range (n + 1), x s * K (n + 1 - s) =
          ∑ s ∈ range (n + 1), y s * K (n + 1 - s) :=
        sum_congr rfl fun s hs => by
          rw [mem_range] at hs
          rw [IH s (by omega)]
      rw [hsum] at h1
      exact add_left_cancel (h1.trans h2.symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)

/-- **The right-bubble moments at nonpositive heights.** At colours `i` with
`hᵢ(μ) ≤ 0`, the normalized right bubbles `c_(μ,i) · bubRs(s)` (even) and
`c_(μ,i) · bubRs(2s)` (odd) act through `raw` as the coefficients of the moment series
`(1-z)^(M_i)/E_i(-z)`, resp. `(1+z)^(M_i)/C_i(-z)`, and the odd bubble acts as
`(-1)^(N_i+1) δ_i`. -/
structure VacuumRightBubblesNonpositiveHeight {μ : X} (A : UpwardModuleAction.{u, w} D Sc μ)
    (t : List I) (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N : I → ℕ) : Prop where
  right_even : ∀ i, D.parity i = 0 → D.h i μ ≤ 0 → ∀ s : ℕ,
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  right_odd : ∀ i, D.parity i = 1 → D.h i μ ≤ 0 → ∀ s : ℕ,
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  oddBubble : ∀ i : {i : I // D.parity i = 1}, D.h i.1 μ ≤ 0 →
    A.closedAct t (SKM.oddBubble cs i μ) = raw (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)

namespace VacuumRightBubblesNonpositiveHeight
variable {cs} {μ : X} {A : UpwardModuleAction.{u, w} D Sc μ} {t : List I}
  {raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)} {M N : I → ℕ}

private theorem normalized_left (i : I) (a b : ℤ) :
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ b) *
      A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ a) =
      A.closedAct t (SKM.bubRs cs i μ a ≫ SKM.bubLs cs i μ b) := by
  rw [show A.closedAct t (SKM.bubRs cs i μ a ≫ SKM.bubLs cs i μ b) =
      A.closedAct t (SKM.bubLs cs i μ b) * A.closedAct t (SKM.bubRs cs i μ a) from
    (A.closedAct t).map_mul (SKM.bubLs cs i μ b : End ((SKM.pres D Sc).obj (SKM.ob D μ [])))
      (SKM.bubRs cs i μ a)]
  rw [map_smul, map_smul, smul_mul_smul_comm]
  rw [show (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]

private theorem left_zero (i : I) :
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ ((0 : ℕ) : ℤ)) = 1 := by
  simp only [Nat.cast_zero, SKM.bubLs_zero, smul_smul]
  rw [show (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]
  exact (A.closedAct t).map_one

private theorem right_zero (i : I) :
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ ((0 : ℕ) : ℤ)) = 1 := by
  simp only [Nat.cast_zero, SKM.bubRs_zero, smul_smul]
  rw [show (cs.c μ i : k) * (↑(cs.c μ i)⁻¹ : k) = 1 by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]
  exact (A.closedAct t).map_one

private theorem raw_substituted_zero (i : I) :
    raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff 0
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    VacuumSeries.coeff_zero_substitutedSeries k (SKM.SYM.constantCoeff_probeSeries D k M),
    map_one, map_one]

/-- **Left even bubbles from the right moments.** -/
theorem left_even (h : VacuumRightBubblesNonpositiveHeight cs A t raw M N) (i : I)
    (hi : D.parity i = 0) (hμ : D.h i μ ≤ 0) (s : ℕ) :
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))) := by
  refine eq_of_sum_mul_eq_zero_right
    (x := fun s : ℕ => A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ s))
    (K := fun s : ℕ => A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ s))
    (y := fun s => raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))))
    (right_zero i) (left_zero i) raw_substituted_zero ?_ ?_ s
  · intro n hn
    simp only [normalized_left]
    rw [← map_sum]
    have e : ∑ r ∈ range (n + 1), SKM.bubRs cs i μ (((n - r : ℕ) : ℤ)) ≫
        SKM.bubLs cs i μ ((r : ℤ)) =
        ∑ r ∈ range (n + 1), SKM.bubRs cs i μ (((n : ℤ) - r)) ≫ SKM.bubLs cs i μ (r) :=
      sum_congr rfl fun r hr => by
        rw [mem_range] at hr
        rw [Nat.cast_sub (by omega)]
    rw [e, SKM.eq_5_5 cs i μ hi n hn, map_zero]
  · intro n hn
    simp only [h.right_even i hi hμ]
    exact AdjunctionBubbleSeries.raw_sum_mul_eq_zero (raw := raw) i n hn

/-- **Left odd bubbles from the right moments.** -/
theorem left_odd (h : VacuumRightBubblesNonpositiveHeight cs A t raw M N) (i : I)
    (hi : D.parity i = 1) (hμ : D.h i μ ≤ 0) (s : ℕ) :
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))) := by
  refine eq_of_sum_mul_eq_zero_right
    (x := fun s : ℕ => A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ (2 * s)))
    (K := fun s : ℕ => A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ (2 * s)))
    (y := fun s => raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))))
    ?_ ?_ raw_substituted_zero ?_ ?_ s
  · simpa only [Nat.cast_zero, mul_zero] using right_zero (A := A) (t := t) (cs := cs) i
  · simpa only [Nat.cast_zero, mul_zero] using left_zero (A := A) (t := t) (cs := cs) i
  · intro n hn
    simp only [normalized_left]
    rw [← map_sum]
    have e : ∑ r ∈ range (n + 1), SKM.bubRs cs i μ (2 * ((n - r : ℕ) : ℤ)) ≫
        SKM.bubLs cs i μ (2 * (r : ℤ)) =
        ∑ r ∈ range (n + 1),
          SKM.bubRs cs i μ (2 * ((n : ℤ) - r)) ≫ SKM.bubLs cs i μ (2 * r) :=
      sum_congr rfl fun r hr => by
        rw [mem_range] at hr
        rw [Nat.cast_sub (by omega)]
    rw [e, SKM.eq_5_6 cs i μ hi n hn, map_zero]
  · intro n hn
    simp only [h.right_odd i hi hμ]
    exact AdjunctionBubbleSeries.raw_sum_mul_eq_zero (raw := raw) i n hn

/-- **The nonpositive-height bubble hypothesis from the right moments.** -/
theorem toNonpositiveHeight (h : VacuumRightBubblesNonpositiveHeight cs A t raw M N) :
    VacuumBubblesNonpositiveHeight cs A t raw M N where
  left_even := h.left_even
  left_odd := h.left_odd
  oddBubble := h.oddBubble

end VacuumRightBubblesNonpositiveHeight

end OddMath.QuiverHecke

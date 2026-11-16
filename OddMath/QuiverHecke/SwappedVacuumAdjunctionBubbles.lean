/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumBubbleSeries
import OddMath.SKM.GrassmannianOdd

/-!
# The right-bubble moments from the left-bubble series

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. This file isolates the
input of `VacuumMoments` that the generator images still have to supply, and derives
`VacuumMoments` from it.

In the swapped construction the closed bubbles at the vacuum are composites of the
cup and cap images, which come from the units and counits of the adjunctions between
the `homContent` functors (`ProbeReservoir.cupImage`, `ProbeReservoir.capImage`). On the
probe and reservoir summands the left bubbles (leftward cup, with the sign `-q` of the
corrected equal-colour crossing entry, then rightward cap with dots) have the
generating series
`B_i(z) = E_i(-z)/(1-z)^(P_i)` at even colours and `C_i(-z)/(1+z)^(M_i)` at odd colours,
which is the substituted series `G_i(-z) u_i(z)` of `VacuumSeries.substitutedSeries`
with `u = SYM.probeSeries M`. The odd bubble acts as `(-1)^(N_i+1) δ_i`.
`AdjunctionBubbleSeries` records exactly these values, for the normalized left bubbles
`c_(μ,i)⁻¹ · bubLs(l)` (even) and `c_(μ,i)⁻¹ · bubLs(2l)` (odd) acting on the source
sector of an upward action.

The right series `B'_i(z) = (1-z)^(P_i)/E_i(-z)` (resp. `(1+z)^(M_i)/C_i(-z)`) is not
assumed. The infinite Grassmannian relations (5.5), (5.6) of Brundan–Ellis hold in the
presented 2-category (`SKM.eq_5_5`, `SKM.eq_5_6`), so in every action; since `B_i`
has constant term one, they determine the right bubbles as the coefficients of
`B_i⁻¹ = B'_i`, which is the moment series (`AdjunctionBubbleSeries.vacuumMoments`).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Finset
universe u

/-- Two sequences `x, y` with `x₀ = y₀ = 1`, each a right inverse of the series `K`
with `K₀ = 1` (`Σ_(s ≤ n) K_s x_(n-s) = 0` for `n > 0`), are equal. -/
theorem eq_of_sum_mul_eq_zero_left {R : Type*} [Ring R] {x y K : ℕ → R} (hK : K 0 = 1)
    (hx0 : x 0 = 1) (hy0 : y 0 = 1)
    (hx : ∀ n, 0 < n → ∑ s ∈ range (n + 1), K s * x (n - s) = 0)
    (hy : ∀ n, 0 < n → ∑ s ∈ range (n + 1), K s * y (n - s) = 0) (n : ℕ) : x n = y n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases n with _ | n
    · rw [hx0, hy0]
    · have h1 := hx (n + 1) n.succ_pos
      have h2 := hy (n + 1) n.succ_pos
      rw [sum_range_succ', Nat.sub_zero, hK, one_mul] at h1 h2
      have hsum : ∑ s ∈ range (n + 1), K (s + 1) * x (n + 1 - (s + 1)) =
          ∑ s ∈ range (n + 1), K (s + 1) * y (n + 1 - (s + 1)) :=
        sum_congr rfl fun s hs => by
          rw [mem_range] at hs
          rw [IH _ (by omega)]
      rw [hsum] at h1
      exact add_left_cancel (h1.trans h2.symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)

/-- The left-bubble series `B_i(z)` of the `homContent` adjunctions at probe exponents
`M` and reservoir levels `N`, acting on the source sector of an upward action through the
raw coefficient action `raw`, together with the odd bubble. -/
structure AdjunctionBubbleSeries {μ : X} (A : UpwardModuleAction D Sc μ) (t : List I)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N : I → ℕ) : Prop where
  /-- Even colours: `Σ c⁻¹·bubLs(l) z^l = E_i(-z)/(1-z)^(M_i)`. -/
  left_even : ∀ i (_ : D.parity i = 0) (s : ℕ),
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  /-- Odd colours: `Σ c⁻¹·bubLs(2l) z^l = C_i(-z)/(1+z)^(M_i)`. -/
  left_odd : ∀ i (_ : D.parity i = 1) (s : ℕ),
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  /-- The odd bubble acts as `(-1)^(N_i+1) δ_i`. -/
  oddBubble : ∀ i : {i : I // D.parity i = 1},
    A.closedAct t (SKM.oddBubble cs i μ) = raw (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)

namespace AdjunctionBubbleSeries
variable {cs} {μ : X} {A : UpwardModuleAction D Sc μ} {t : List I}
  {raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)} {M N : I → ℕ}

theorem coeff_zero_momentSeries (i : I) :
    PowerSeries.coeff 0 (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i) = 1 := by
  have h := congrArg (PowerSeries.coeff 0)
    (VacuumSeries.substitutedSeries_mul_momentSeries k (SKM.SYM.probeSeries_mul_inv D k M) i)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    VacuumSeries.coeff_zero_substitutedSeries k (SKM.SYM.constantCoeff_probeSeries D k M),
    one_mul, PowerSeries.coeff_one] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h]; simp

/-- The raw moments are a right inverse of the raw left series. -/
theorem raw_sum_mul_eq_zero (i : I) (n : ℕ) (hn : 0 < n) :
    ∑ s ∈ range (n + 1), raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))) *
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff (n - s)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))) = 0 := by
  simp_rw [← map_mul, ← map_sum]
  have e : ∑ s ∈ range (n + 1), PowerSeries.coeff s
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i) *
      PowerSeries.coeff (n - s) (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i) =
      PowerSeries.coeff n (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i *
        VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [e, VacuumSeries.substitutedSeries_mul_momentSeries k (SKM.SYM.probeSeries_mul_inv D k M),
    PowerSeries.coeff_one]
  simp [hn.ne']

/-- The closed action of a composite of closed diagrams is the product, in reverse order. -/
theorem closedAct_comp (f g : (SKM.pres D Sc).obj (SKM.ob D μ []) ⟶
    (SKM.pres D Sc).obj (SKM.ob D μ [])) :
    A.closedAct t (f ≫ g) = A.closedAct t g * A.closedAct t f := by
  exact (A.closedAct t).map_mul (g : End ((SKM.pres D Sc).obj (SKM.ob D μ []))) f

/-- The normalized product of a right and a left bubble. -/
theorem closedAct_normalized (i : I) (a b : ℤ) :
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ b) *
      A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ a) =
      A.closedAct t (SKM.bubRs cs i μ a ≫ SKM.bubLs cs i μ b) := by
  rw [closedAct_comp, map_smul, map_smul, smul_mul_smul_comm]
  rw [show (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]

/-- **(12) at even colours**: the normalized right bubbles are the coefficients of the
moment series `(1-z)^(M_i)/E_i(-z)`. -/
theorem right_even (h : AdjunctionBubbleSeries cs A t raw M N) (i : I) (hi : D.parity i = 0)
    (s : ℕ) :
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))) := by
  refine eq_of_sum_mul_eq_zero_left
    (x := fun s => A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ s))
    (K := fun s => A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ s))
    (y := fun s => raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    ?_ ?_ ?_ ?_ ?_ s
  · simp only [Nat.cast_zero, SKM.bubLs_zero, smul_smul]
    rw [show (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]
    exact (A.closedAct t).map_one
  · simp only [Nat.cast_zero, SKM.bubRs_zero, smul_smul]
    rw [show (cs.c μ i : k) * (↑(cs.c μ i)⁻¹ : k) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]
    exact (A.closedAct t).map_one
  · rw [coeff_zero_momentSeries, map_one, map_one]
  · intro n hn
    simp only [closedAct_normalized]
    rw [← map_sum]
    have e : ∑ r ∈ range (n + 1), SKM.bubRs cs i μ (((n - r : ℕ) : ℤ)) ≫
        SKM.bubLs cs i μ ((r : ℤ)) =
        ∑ r ∈ range (n + 1), SKM.bubRs cs i μ (((n : ℤ) - r)) ≫ SKM.bubLs cs i μ (r) :=
      sum_congr rfl fun r hr => by
        rw [mem_range] at hr
        rw [Nat.cast_sub (by omega)]
    rw [e, SKM.eq_5_5 cs i μ hi n hn, map_zero]
  · intro n hn
    simp only [h.left_even i hi]
    exact raw_sum_mul_eq_zero i n hn

/-- **(12) at odd colours**: the normalized right bubbles with even dot counts are the
coefficients of the moment series `(1+z)^(M_i)/C_i(-z)`. -/
theorem right_odd (h : AdjunctionBubbleSeries cs A t raw M N) (i : I) (hi : D.parity i = 1)
    (s : ℕ) :
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))) := by
  refine eq_of_sum_mul_eq_zero_left
    (x := fun s : ℕ => A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ (2 * s)))
    (K := fun s : ℕ => A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ (2 * s)))
    (y := fun s => raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    ?_ ?_ ?_ ?_ ?_ s
  · simp only [Nat.cast_zero, mul_zero, SKM.bubLs_zero, smul_smul]
    rw [show (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]
    exact (A.closedAct t).map_one
  · simp only [Nat.cast_zero, mul_zero, SKM.bubRs_zero, smul_smul]
    rw [show (cs.c μ i : k) * (↑(cs.c μ i)⁻¹ : k) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]
    exact (A.closedAct t).map_one
  · rw [coeff_zero_momentSeries, map_one, map_one]
  · intro n hn
    simp only [closedAct_normalized]
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
    simp only [h.left_odd i hi]
    exact raw_sum_mul_eq_zero i n hn

/-- **The moment hypothesis from the left-bubble series.** -/
theorem vacuumMoments (h : AdjunctionBubbleSeries cs A t raw M N) :
    VacuumMoments cs A t raw M N where
  even := h.right_even
  odd := h.right_odd
  oddBubble := h.oddBubble

/-- (A16) from the left-bubble series: the source-placed bubble algebra acts through
`raw ∘ θ`. -/
theorem bubbles_eq (h : AdjunctionBubbleSeries cs A t raw M N) (a : SKM.SYM D k) :
    A.bubbles cs t a = raw (SKM.SYM.probeSubstitution D k M N a) :=
  h.vacuumMoments.bubbles_eq a

end AdjunctionBubbleSeries

end OddMath.QuiverHecke

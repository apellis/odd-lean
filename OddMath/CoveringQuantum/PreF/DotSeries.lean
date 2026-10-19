/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import OddMath.CoveringQuantum.HalfAlgebra

/-!
# Formal dot factors for positive words

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 10.3, Claim 1:
a strand of colour `i` contributes the factor `1 / (1 - πᵢ qᵢ²)`.
Here `X` is the formal grading variable, so `qᵢ²` means `X^(2*dᵢ)`.

`PreF.DotSeries.factor` is the positive-exponent geometric series, constructed
with Mathlib's `PowerSeries.expand`. Its coefficients are `a^c` at degree `e*c`
and zero off the multiples of `e`. `coeff_strands` computes every coefficient
of a finite product by a **finite antidiagonal sum**, not an infinite sum in a
rational coefficient field. The `countEnergy` lemmas identify its divisible
indices bijectively with dot counts, retaining a separate count for each strand,
even when colours repeat.

`SuperCartanDatum.dotSeries` specializes this construction to a word `Fin n → I`,
with degree increment `2*dᵢ` and weight `pii π i`. No finiteness assumption on the
colour type is needed. The denominator is a unit in the power-series ring, and
`dotSeries_eq_prod_inverse` identifies its inverse expansion. The polynomial
`dotDenominator` also recovers the existing `norm` by **polynomial** evaluation
and `Ring.inverse`; this does not evaluate arbitrary series or rational functions.

This proves only the formal dot-factor step. Identification with decorated
diagrams, crossing factors (which may have negative degree), and the full
comparison of the graphical and algebraic forms remain separate. No claim about
specializing the whole field `ℚ(q)` or removing the algebraic form's finiteness
and bar-consistency hypotheses is made.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.CoveringQuantum.PreF
namespace DotSeries
variable {k : Type*} [CommRing k]

/-- One strand with weight `a` per dot and positive degree increment `e`. -/
def factor (a : k) (e : ℕ) (he : e ≠ 0) : PowerSeries k :=
  PowerSeries.expand e he (PowerSeries.mk fun n ↦ a ^ n)

/-- The geometric series is an inverse of its formal denominator. -/
theorem factor_mul (a : k) (e : ℕ) (he : e ≠ 0) :
    factor a e he * (1 - PowerSeries.C a * PowerSeries.X ^ e) = 1 := by
  have h := congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one k)
  have h' : (PowerSeries.mk fun n ↦ a ^ n) * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
    simpa [PowerSeries.rescale_mk, PowerSeries.rescale_X] using h
  have := congrArg (PowerSeries.expand e he) h'
  simpa [factor, map_mul, map_sub, PowerSeries.expand_C] using this

/-- Coefficientwise geometric expansion; no topology or infinite scalar sum is used. -/
theorem coeff_factor (a : k) (e : ℕ) (he : e ≠ 0) (m : ℕ) :
    PowerSeries.coeff m (factor a e he) = if e ∣ m then a ^ (m / e) else 0 := by
  by_cases h : e ∣ m
  · obtain ⟨n, rfl⟩ := h
    simp [factor, Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero he)]
  · simp [factor, PowerSeries.coeff_expand_of_not_dvd, h]

/-- The explicit geometric expansion agrees with the ring inverse. -/
theorem factor_eq_inverse (a : k) (e : ℕ) (he : e ≠ 0) :
    factor a e he = Ring.inverse (1 - PowerSeries.C a * PowerSeries.X ^ e) := by
  have hu : IsUnit (1 - PowerSeries.C a * PowerSeries.X ^ e : PowerSeries k) :=
    isUnit_iff_exists_inv.mpr ⟨factor a e he, by rw [mul_comm]; exact factor_mul a e he⟩
  simpa using (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hu).2 (by simpa using factor_mul a e he)

variable {ι : Type*} [Fintype ι]

/-- Independent dot factors indexed by finite strand positions, not by colours. -/
def strands (a : ι → k) (e : ι → ℕ) (he : ∀ i, e i ≠ 0) : PowerSeries k :=
  ∏ i, factor (a i) (e i) (he i)

/-- Each coefficient is a finite sum over allocations of total degree. -/
theorem coeff_strands [DecidableEq ι] (a : ι → k) (e : ι → ℕ) (he : ∀ i, e i ≠ 0) (m : ℕ) :
    PowerSeries.coeff m (strands a e he) =
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ m,
        ∏ i, if e i ∣ l i then a i ^ (l i / e i) else 0 := by
  simp only [strands, PowerSeries.coeff_prod, coeff_factor]

theorem strands_mul (a : ι → k) (e : ι → ℕ) (he : ∀ i, e i ≠ 0) :
    strands a e he * (∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X ^ e i)) = 1 := by
  rw [strands, ← Finset.prod_mul_distrib]
  simp [factor_mul]

theorem strands_eq_prod_inverse (a : ι → k) (e : ι → ℕ) (he : ∀ i, e i ≠ 0) :
    strands a e he = ∏ i, Ring.inverse (1 - PowerSeries.C (a i) * PowerSeries.X ^ e i) := by
  simp only [strands, factor_eq_inverse]

/-- Convert a dot-count vector to the degree allocation used by the antidiagonal. -/
def countEnergy (e c : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ e i * c i

@[simp] theorem countEnergy_apply (e c : ι → ℕ) (i : ι) :
    countEnergy e c i = e i * c i := by simp [countEnergy]

/-- The antidiagonal condition is precisely the total dot-degree condition. -/
theorem countEnergy_mem [DecidableEq ι] (e c : ι → ℕ) (m : ℕ) :
    countEnergy e c ∈ Finset.finsuppAntidiag Finset.univ m ↔ ∑ i, e i * c i = m := by
  simp [Finset.mem_finsuppAntidiag]

/-- Positive increments ensure that distinct dot counts give distinct allocations. -/
theorem countEnergy_injective (e : ι → ℕ) (he : ∀ i, e i ≠ 0) :
    Function.Injective (countEnergy e) := by
  intro c d h
  funext i
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (he i))
    (by simpa using DFunLike.congr_fun h i)

/-- Every divisible degree allocation arises from dot counts. -/
theorem exists_countEnergy_iff (e : ι → ℕ) (l : ι →₀ ℕ) :
    (∃ c, countEnergy e c = l) ↔ ∀ i, e i ∣ l i := by
  constructor
  · rintro ⟨c, rfl⟩ i
    simp
  · intro h
    refine ⟨fun i ↦ l i / e i, ?_⟩
    ext i
    simp [Nat.mul_div_cancel' (h i)]

/-- The summand belonging to a dot-count vector is the product of its parity weights. -/
theorem prod_coeff_countEnergy (a : ι → k) (e c : ι → ℕ) (he : ∀ i, e i ≠ 0) :
    (∏ i, PowerSeries.coeff (countEnergy e c i) (factor (a i) (e i) (he i))) =
      ∏ i, a i ^ c i := by
  simp [coeff_factor, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (he _))]

end DotSeries
end OddMath.CoveringQuantum.PreF

namespace OddMath.CoveringQuantum.SuperCartanDatum
open PreF.DotSeries
variable {I k : Type*} [CommRing k] (C : SuperCartanDatum I) (π : k)

/-- The denominator polynomial underlying both the formal factor and the existing norm. -/
def dotDenominator (i : I) : Polynomial k :=
  1 - Polynomial.C (C.pii π i) * Polynomial.X ^ (2 * C.d i)

/-- Compatibility with the existing norm, evaluating only a finite polynomial. -/
theorem norm_eq_inverse_eval_dotDenominator (q : kˣ) (i : I) :
    C.norm q π i = Ring.inverse ((C.dotDenominator π i).eval (q : k)) := by
  simp [dotDenominator, norm, qi, ← pow_mul, Nat.mul_comm]

/-- The dot-generating series for the strands of a positive word. -/
def dotSeries {n : ℕ} (word : Fin n → I) : PowerSeries k :=
  strands (fun r ↦ C.pii π (word r)) (fun r ↦ 2 * C.d (word r))
    (fun r ↦ Nat.ne_of_gt (by have := C.d_pos (word r); omega))

/-- The dot-factor product in BE2 Theorem 10.3, Claim 1, interpreted as formal series. -/
theorem dotSeries_eq_prod_inverse {n : ℕ} (word : Fin n → I) :
    C.dotSeries π word = ∏ r, Ring.inverse
      (1 - PowerSeries.C (C.pii π (word r)) * PowerSeries.X ^ (2 * C.d (word r))) :=
  strands_eq_prod_inverse _ _ _

/-- Finite coefficientwise interpretation of the dot-factor product for a positive word. -/
theorem coeff_dotSeries {n : ℕ} (word : Fin n → I) (m : ℕ) :
    PowerSeries.coeff m (C.dotSeries π word) =
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ m,
        ∏ r, if 2 * C.d (word r) ∣ l r then
          C.pii π (word r) ^ (l r / (2 * C.d (word r))) else 0 :=
  coeff_strands _ _ _ _

/-- The finite product of denominator polynomials cancels the dot-generating series. -/
theorem dotSeries_mul_denominator {n : ℕ} (word : Fin n → I) :
    C.dotSeries π word *
      (∏ r, (C.dotDenominator π (word r) : PowerSeries k)) = 1 := by
  simpa [dotDenominator, dotSeries] using strands_mul
    (fun r ↦ C.pii π (word r)) (fun r ↦ 2 * C.d (word r))
    (fun r ↦ Nat.ne_of_gt (by have := C.d_pos (word r); omega))

@[simp] theorem dotSeries_empty (word : Fin 0 → I) : C.dotSeries π word = 1 := by
  simp [dotSeries, strands]

/-- Each denominator is invertible in formal series because its constant coefficient is one. -/
theorem dotDenominator_isUnit (i : I) :
    IsUnit (C.dotDenominator π i : PowerSeries k) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp [dotDenominator, Nat.ne_of_gt (C.d_pos i)]

/-- The contribution of a fixed dot-count vector, before summing over vectors. -/
theorem dotCount_monomial {n : ℕ} (word : Fin n → I) (c : Fin n → ℕ) :
    (∏ r, PowerSeries.monomial (2 * C.d (word r) * c r) (C.pii π (word r) ^ c r)) =
      PowerSeries.monomial (∑ r, 2 * C.d (word r) * c r) (∏ r, C.pii π (word r) ^ c r) :=
  PowerSeries.prod_monomial _ _ _

end OddMath.CoveringQuantum.SuperCartanDatum

namespace OddMath.CoveringQuantum.PreF.DotSeries

/-! Empty words, odd parity, absent odd degrees, and two repeated colours. -/

example : strands (fun _ : Fin 0 ↦ (-1 : ℤ)) (fun _ ↦ 2) (fun _ ↦ by decide) = 1 := by
  simp [strands]

example : PowerSeries.coeff 2 (factor (-1 : ℤ) 2 (by decide)) = -1 := by
  norm_num [coeff_factor]

example : PowerSeries.coeff 3 (factor (-1 : ℤ) 2 (by decide)) = 0 := by
  norm_num [coeff_factor]

example : PowerSeries.coeff 2
    (strands (fun _ : Fin 2 ↦ (-1 : ℤ)) (fun _ ↦ 2) (fun _ ↦ by decide)) = -2 := by
  simp only [strands, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_two, PowerSeries.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, coeff_factor]
end OddMath.CoveringQuantum.PreF.DotSeries

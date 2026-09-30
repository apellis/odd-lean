import OddMath.Frontier.EQSchurDifferential
import OddMath.Frontier.EQZnAction

/-!
# The longest element on odd elementary polynomials: (2.20) and (2.22)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.4.1, equations (2.19)–(2.22).

`w₀` is the plain permutation action `w₀(x_i) = x_{n+1-i}` (`EQSkewDifferential.longestPerm`),
`θ(x_i) = (-1)^{i-1} x_i` the twisting (2.19) (`EQSkewDifferential.theta`, strands numbered from
`0`), `e_k` the untwisted odd elementary polynomial (`EQSkewDifferential.elementary`) and
`ẽ_k = θ(e_k)` the twisted one, which is EKL's elementary polynomial
`FiniteCompleteElementary.elementaryPoly` (`theta_elementary`).

* **(2.20)** (`longestPerm_elementary`): `w₀(e_k) = (-1)^{binom(k,2)} e_k`, for all `n`, `k`.
* **(2.22)** (`eq_2_22`): `w₀(ẽ_k) = (-1)^{(n+1)k} (θ ∘ w₀) θ(ẽ_k) = (-1)^{(n+1)k + binom(k,2)} ẽ_k`,
  as printed, for all `n`, `k`. It follows from (2.21) (`EQSchur.theta_longestPerm`) with
  `f = e_k` of parity `k` and (2.20); in terms of EKL's `elementaryPoly` this is
  `eq_2_22_elementaryPoly`.
* The left-hand side of (2.22) is the *twisted* `w₀(ẽ_k)`: with the untwisted `w₀(e_k)` on the
  left the identity fails (already for `n = 2`, `k = 1`: `w₀(e_1) = e_1 = x_1 + x_2` while
  `-ẽ_1 = x_2 - x_1`), see `eq_2_22_untwisted_false`; the untwisted element is governed by (2.20).
-/

namespace OddMath.Frontier.EQFix

open OddMath.SkewPolynomial (SkewPolynomial generator expSingle)
open OddMath.Frontier.EQSkewDifferential (theta longestPerm twistRev elementary parityInv
  parityInv_elementary)
open FiniteCompleteElementary
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqFixW0NUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqFixW0NUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- `ẽ_k = θ(e_k)` is EKL's odd elementary polynomial (Ellis–Qi, Remark 2.14). -/
theorem theta_elementary (n k : ℕ) :
    theta n (elementary n k) = FiniteCompleteElementary.elementaryPoly n k := by
  rw [elementary, EQZn.ringHom_strictSum]
  have h : (fun j : Fin n => theta n (generator j)) = PlacticEvaluation.tildeGenerator := by
    funext j
    rw [EQSkewDifferential.theta_generator, PlacticEvaluation.tildeGenerator]
  rw [h, EQZn.strictSum_tilde]

theorem neg_one_pow_add_two_mul (a b : ℕ) : (-1 : ℤ) ^ (a + 2 * b) = (-1) ^ a := by
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Ellis–Qi (2.20)**: `w₀(e_k) = (-1)^{binom(k,2)} e_k`, for all `n` and `k`. -/
theorem longestPerm_elementary (n k : ℕ) :
    longestPerm n (elementary n k) = (-1 : ℤ) ^ k.choose 2 • elementary n k := by
  have h := congrArg (theta n) (EQZn.twistRev_elementary n k)
  rw [twistRev, RingHom.comp_apply, EQSchur.theta_theta, map_zsmul, ← theta_elementary,
    EQSchur.theta_theta] at h
  rw [h, show (n - 1).choose 2 * k + (k.choose 2 + k * (n - 1).choose 2) =
    k.choose 2 + 2 * ((n - 1).choose 2 * k) by ring, neg_one_pow_add_two_mul]

/-- **Ellis–Qi (2.22)**, as printed: `w₀(ẽ_k) = (-1)^{(n+1)k} (θ ∘ w₀) θ(ẽ_k)` and
`w₀(ẽ_k) = (-1)^{(n+1)k + binom(k,2)} ẽ_k`, where `ẽ_k = θ(e_k)`, for all `n` and `k`. -/
theorem eq_2_22 (n k : ℕ) :
    longestPerm n (theta n (elementary n k)) =
        (-1 : ℤ) ^ ((n + 1) * k) • twistRev n (theta n (theta n (elementary n k))) ∧
      longestPerm n (theta n (elementary n k)) =
        (-1 : ℤ) ^ ((n + 1) * k + k.choose 2) • theta n (elementary n k) := by
  -- (2.21) with `f = e_k`, of parity `k`
  have h21 := EQSchur.theta_longestPerm (elementary n k) k (parityInv_elementary k)
  have hmain : longestPerm n (theta n (elementary n k)) =
      (-1 : ℤ) ^ ((n + 1) * k) • twistRev n (elementary n k) := by
    rw [twistRev, RingHom.comp_apply, h21, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul]
  refine ⟨by rw [EQSchur.theta_theta, hmain], ?_⟩
  rw [hmain, twistRev, RingHom.comp_apply, longestPerm_elementary, map_zsmul, smul_smul,
    ← pow_add]

/-- **Ellis–Qi (2.22)** with EKL's elementary polynomials `ẽ_k = elementaryPoly n k`:
`w₀(ẽ_k) = (-1)^{(n+1)k + binom(k,2)} ẽ_k`. -/
theorem eq_2_22_elementaryPoly (n k : ℕ) :
    longestPerm n (FiniteCompleteElementary.elementaryPoly n k) =
      (-1 : ℤ) ^ ((n + 1) * k + k.choose 2) • FiniteCompleteElementary.elementaryPoly n k := by
  rw [← theta_elementary]
  exact (eq_2_22 n k).2

/-- The printed (2.22) has the twisted `ẽ_k` on the left. With the untwisted `e_k` on the left,
`w₀(e_k) = (-1)^{(n+1)k + binom(k,2)} ẽ_k` is false: for `n = 2`, `k = 1`,
`w₀(e_1) = x_1 + x_2` but `(-1)^3 ẽ_1 = x_2 - x_1` (1-indexed). -/
theorem eq_2_22_untwisted_false :
    longestPerm 2 (elementary 2 1) ≠
      (-1 : ℤ) ^ ((2 + 1) * 1 + (1 : ℕ).choose 2) • theta 2 (elementary 2 1) := by
  intro h
  rw [longestPerm_elementary] at h
  have he : elementary 2 1 = generator 0 + generator 1 := by
    rw [elementary, FiniteWords.strictSum_succ, FiniteWords.strictSum_zero, mul_one,
      FiniteWords.strictSum_succ, FiniteWords.strictSum_zero, mul_one]
    simp
  rw [he, map_add, EQSkewDifferential.theta_generator, EQSkewDifferential.theta_generator] at h
  have hc := congrArg (fun p : SkewPolynomial 2 => p (expSingle 0)) h
  simp [OddMath.SkewPolynomial.generator] at hc

end

end OddMath.Frontier.EQFix

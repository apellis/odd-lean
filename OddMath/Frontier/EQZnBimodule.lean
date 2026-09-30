import OddMath.Frontier.EQZnFiniteCell
import OddMath.Frontier.OddSymmetrizer

/-!
# The right `OΛ_n`-action on `ONH_n e_n` (Lemma 2.18, Proposition 3.7)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.3 (Lemma 2.17 (1), Lemma 2.18 (2.44)) and §3.2 (Proposition 3.7).

Rank `N = n + 2`, strands numbered from `0`, `x^δ = x_0^{N-1} x_1^{N-2} ⋯ x_{N-2}`
(`LongestDivided.staircase`), `e_N = (-1)^{binom(N,3)} ∂_{w₀} x^δ` (`eqIdempotent`).

* `staircase_mul` (Lemma 2.17 (1)): `x^δ f = θ'(f) x^δ` for every `f ∈ OPol_N`, where
  `θ'(x_i) = (-1)^{binom(N-1,2)} (-1)^i x_i`; equivalently `f x^δ = ± x^δ θ(f)` for homogeneous `f`.
* `eqIdempotent_mul_polyElem` (**Lemma 2.18**, (2.44)): `e_N f = (θ ∘ w₀)(f) e_N` in `ONH_N` for
  every untwisted odd symmetric `f ∈ OΛ_N`.
* `proposition_3_7`: `OPol_N e_N` is a dg `(OPol_N, OΛ_N)`-bimodule isomorphic to
  `Z_N = OPol_N(0,1,0,1,…)` with right action `g e_N · f = g (θ ∘ w₀)(f) e_N`.
-/

namespace OddMath.Frontier.EQZn

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential
open NilHeckeAction
open OddMath.Diagrams.OddNilHecke (dONH eqIdempotent)
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) znBimNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) znBimNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

theorem neg_one_pow_eq_of_even_add {a b : ℕ} (h : Even (a + b)) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  have hs : (-1 : ℤ) ^ a * (-1) ^ b = 1 := by rw [← pow_add, h.neg_one_pow]
  have hb : (-1 : ℤ) ^ b * (-1) ^ b = 1 := neg_one_pow_mul_self' b
  calc (-1 : ℤ) ^ a = (-1) ^ a * ((-1) ^ b * (-1) ^ b) := by rw [hb, mul_one]
    _ = (-1) ^ b := by rw [← mul_assoc, hs, one_mul]

theorem sum_staircase_exponent (N : ℕ) : ∑ i : Fin N, (N - 1 - i.val) = N.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i), Nat.choose_two_right]
  rw [show (∑ i ∈ Finset.range N, (N - 1 - i)) = ∑ i ∈ Finset.range N, i from
    Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]

/-- The sign `(-1)^{binom(N-1,2)}` in `x^δ x_i = (-1)^{binom(N-1,2)} (-1)^i x_i x^δ`. -/
def stairSign (N : ℕ) : ℤ := (-1 : ℤ) ^ (N - 1).choose 2

/-- `x^δ x_i = (-1)^{binom(N-1,2)} (-1)^i x_i x^δ`. -/
theorem staircase_mul_generator (i : Fin (n+2)) :
    LongestDivided.staircase (n+2) * generator i =
      (stairSign (n+2) * (-1 : ℤ) ^ i.val) • (generator i * LongestDivided.staircase (n+2)) := by
  have h1 := parityInv_monomial_mul_generator (fun j : Fin (n+2) => n + 2 - 1 - j.val) i
  rw [parityInv_monomial, sum_staircase_exponent, smul_mul_assoc] at h1
  have h2 := congrArg (fun t => (-1 : ℤ) ^ (n+2).choose 2 • t) h1
  simp only [smul_smul, neg_one_pow_mul_self', one_smul] at h2
  rw [LongestDivided.staircase, h2, stairSign, ← pow_add, ← pow_add]
  congr 1
  apply neg_one_pow_eq_of_even_add
  have hc : (n+2).choose 2 = (n+1).choose 2 + (n+1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hi := i.isLt
  rw [show n + 2 - 1 = n + 1 by omega, hc]
  exact ⟨(n+1).choose 2 + (n + 1) + 0 * i.val, by omega⟩

/-- `θ'(x_i) = (-1)^{binom(N-1,2)} (-1)^i x_i`. -/
def thetaStair (n : ℕ) : SkewPolynomial (n+2) →+* SkewPolynomial (n+2) :=
  skewLift (fun j => (stairSign (n+2) * (-1 : ℤ) ^ j.val) • generator (Equiv.refl _ j))
    (fun i j h => smul_generator_anticomm (fun j => stairSign (n+2) * (-1 : ℤ) ^ j.val)
      (Equiv.refl _) i j h)

@[simp] theorem thetaStair_generator (j : Fin (n+2)) :
    thetaStair n (generator j) = (stairSign (n+2) * (-1 : ℤ) ^ j.val) • generator j := by
  simp [thetaStair]

/-- **Ellis–Qi, Lemma 2.17 (1)**: `x^δ f = θ'(f) x^δ` for every skew polynomial `f`. -/
theorem staircase_mul (f : SkewPolynomial (n+2)) :
    LongestDivided.staircase (n+2) * f = thetaStair n f * LongestDivided.staircase (n+2) := by
  induction f using induction_generator with
  | hgen j => rw [staircase_mul_generator, thetaStair_generator, smul_mul_assoc]
  | h0 => simp
  | h1 => simp
  | hadd f g hf hg => rw [mul_add, hf, hg, map_add, add_mul]
  | hneg f hf => rw [mul_neg, hf, map_neg, neg_mul]
  | hmul f g hf hg => rw [← mul_assoc, hf, mul_assoc, hg, map_mul, mul_assoc]

theorem thetaStair_elementary (k : ℕ) :
    thetaStair n (elementary (n+2) k) =
      (stairSign (n+2)) ^ k • FiniteCompleteElementary.elementaryPoly (n+2) k := by
  rw [elementary, ringHom_strictSum]
  have h : (fun j : Fin (n+2) => thetaStair n (generator j)) =
      fun j => stairSign (n+2) • PlacticEvaluation.tildeGenerator j := by
    funext j
    rw [thetaStair_generator, PlacticEvaluation.tildeGenerator, smul_smul]
  rw [h, strictSum_zsmul, strictSum_tilde]

theorem elementaryPoly_mem_kernel (k : ℕ) :
    FiniteCompleteElementary.elementaryPoly (n+2) k ∈ OddSymmetricKernel.kernelSubring n := by
  rw [← StaircaseIndependence.E_eq_kernel]
  exact Subring.subset_closure ⟨k, rfl⟩

/-- **Ellis–Qi, Lemma 2.18** on `OPol_N`: `∂_{w₀}(x^δ f g) = (θ ∘ w₀)(f) ∂_{w₀}(x^δ g)` for
`f ∈ OΛ_N` and every `g`. -/
theorem D_staircase_mul_osym {f : SkewPolynomial (n+2)} (hf : f ∈ osym (n+2))
    (g : SkewPolynomial (n+2)) :
    LongestDivided.D (n+2) (LongestDivided.staircase (n+2) * (f * g)) =
      twistRev (n+2) f * LongestDivided.D (n+2) (LongestDivided.staircase (n+2) * g) := by
  induction hf using Subring.closure_induction generalizing g with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [← mul_assoc, staircase_mul (elementary (n+2) k), thetaStair_elementary, smul_mul_assoc,
      smul_mul_assoc, mul_assoc, map_zsmul,
      OddSymmetrizer.D_left_kernel n _ _ (elementaryPoly_mem_kernel k),
      LongestElementary.action_elementary, twistRev_elementary, smul_mul_assoc, smul_mul_assoc,
      smul_smul, stairSign, ← pow_mul, ← pow_add]
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [add_mul, mul_add, map_add, hx, hy, map_add, add_mul]
  | neg x _ hx => rw [neg_mul, mul_neg, map_neg, hx, map_neg, neg_mul]
  | mul x y _ _ hx hy => rw [mul_assoc, hx, hy, map_mul (twistRev (n+2)) x y, mul_assoc]

/-- **Ellis–Qi, Lemma 2.18** (2.44): `e_N f = (θ ∘ w₀)(f) e_N` in `ONH_N` for every untwisted odd
symmetric polynomial `f ∈ OΛ_N`. -/
theorem eqIdempotent_mul_polyElem {f : SkewPolynomial (n+2)} (hf : f ∈ osym (n+2)) :
    eqIdempotent n * OnhPolynomial.polyElem n f =
      OnhPolynomial.polyElem n (twistRev (n+2) f) * eqIdempotent n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro g
  rw [action_mul_apply, action_mul_apply, OnhPolynomial.action_polyElem,
    OnhPolynomial.action_polyElem, action_eqIdempotent, action_eqIdempotent,
    D_staircase_mul_osym hf, mul_smul_comm]

/-- **Ellis–Qi, Proposition 3.7**: `OPol_N e_N ⊆ ONH_N` is a dg `(OPol_N, OΛ_N)`-bimodule
isomorphic to `Z_N`: under `f ↦ f e_N` (`toONH`, Corollary 3.6), right multiplication by
`c ∈ OΛ_N` corresponds to the right action `g 1_z · c = g (θ∘w₀)(c) 1_z` of `Z_N`, and the
differential corresponds to `d_{Z_N}` (with the right Leibniz rule `dAlpha_mul_twistRev`). -/
theorem proposition_3_7 :
    (∀ (g : SkewPolynomial (n+2)) {c : SkewPolynomial (n+2)}, c ∈ osym (n+2) →
      toONH n g * OnhPolynomial.polyElem n c = toONH n (g * twistRev (n+2) c)) ∧
    (∀ f : SkewPolynomial (n+2), dONH n (toONH n f) = toONH n (dAlpha (zAlpha (n+2)) f)) := by
  refine ⟨fun g c hc => ?_, corollary_3_6.2.2.2⟩
  rw [toONH_apply, toONH_apply, mul_assoc, eqIdempotent_mul_polyElem hc, ← mul_assoc, ← map_mul]

end

end OddMath.Frontier.EQZn

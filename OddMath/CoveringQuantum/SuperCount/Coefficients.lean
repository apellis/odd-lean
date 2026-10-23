/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.SuperCount.Operator
import OddMath.CoveringQuantum.Ordinary
import LieLean.Algebra.QuantumGroup.GabberKac
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.ShapovalovSign
import LieLean.Algebra.Lie.KacMoody.Super.Enveloping

/-!
# The Verma coefficients of the covering bicharacter at `π = -1`

For the covering bicharacter `χ(i, j) = q^{-i·j} π^{|i||j|}` one has
`χ(i, μ) = qᵢ^{-⟨μ, αᵢ^∨⟩} ∏ₖ (π^{|i||k|})^{μₖ}` (`SuperCartanDatum.chi_wt_single`). At `π = -1`,
with `ψ` the covering bicharacter at `q⁻¹` and suitable scalars `aᵢ`, `bᵢ`, the coefficients
`aᵢ ψ(i, μ) - bᵢ χ(i, μ)` of the raising operators of `OddMath.CoveringQuantum.SuperCount.Operator`
are the images under `T ↦ q` of the Laurent polynomials
`cᵢ(μ) = ∏ₖ ((-1)^{|i||k|})^{μₖ} [nᵢ - ⟨μ, αᵢ^∨⟩]_{T^{dᵢ}}`
(`SuperCartanDatum.raiseCoeff_eq_evalAt`); at `T = 1` these are the classical coefficients
`nᵢ - ⟨μ, αᵢ^∨⟩` twisted by the super sign character (`SuperCartanDatum.evalAt_one_superCoeff`).
These are the coefficients of the super Shapovalov kernel of `LieLean`
(`LusztigF.mem_superSerreIdeal_of_shapovalovMap_eq_zero`). The computation is ours.

## Main definitions

* `SuperCartanDatum.superCoeff C n i μ`: the Laurent polynomial `cᵢ(μ)`.
* `SuperCartanDatum.raiseA`, `SuperCartanDatum.raiseB`: the scalars `aᵢ`, `bᵢ`.

## Main results

* `SuperCartanDatum.chi_wt_single`, `SuperCartanDatum.chi_inv_mul_chi`.
* `SuperCartanDatum.raiseCoeff_eq_evalAt`, `SuperCartanDatum.evalAt_one_superCoeff`.
* `SuperCartanDatum.norm_isUnit_of_transcendental`.
-/

noncomputable section

namespace OddMath.CoveringQuantum.SuperCartanDatum

open LusztigF Matrix.Realization

variable {I k : Type*} (C : SuperCartanDatum I)

/-! ### The covering bicharacter on `αᵢ` -/

section Field

variable [Field k] (q : kˣ) (π : k)

/-- `χ(i, μ) = qᵢ^{-⟨μ, αᵢ^∨⟩} ∏ₖ (π^{|i||k|})^{μₖ}`. -/
theorem chi_wt_single (i : I) (μ : I →₀ ℕ) :
    (C.chi q π).wt (Finsupp.single i 1) μ =
      ((q : k) ^ C.d i) ^ (-C.lusztigDatum.coPairing i μ) *
        weightSign (fun j ↦ π ^ (C.parity i * C.parity j).val) μ := by
  classical
  have hq : (q : k) ≠ 0 := q.ne_zero
  induction μ using Finsupp.induction with
  | zero => simp [Bichar.wt_zero_right]
  | single_add j m μ _ _ ih =>
    rw [Bichar.wt_add_right, ih, weightSign_add, weightSign_single]
    have hc : C.lusztigDatum.coPairing i (Finsupp.single j m + μ) =
        m * C.a i j + C.lusztigDatum.coPairing i μ := by
      rw [LusztigCartanDatum.coPairing, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring),
        Finsupp.sum_single_index (by simp), lusztigDatum_cartanMatrix, ← LusztigCartanDatum.coPairing]
    have hs : (C.chi q π).wt (Finsupp.single i 1) (Finsupp.single j m) =
        (C.chi q π i j) ^ m := by
      simp [Bichar.wt]
    rw [hs, hc, chi_apply, Units.val_zpow_eq_zpow_val, dot, mul_pow]
    have e : ((q : k) ^ (-(↑(C.d i) * C.a i j))) ^ m = ((q : k) ^ C.d i) ^ (-(↑m * C.a i j)) := by
      rw [← zpow_natCast _ m, ← zpow_mul, ← zpow_natCast (q : k) (C.d i), ← zpow_mul]
      ring_nf
    rw [e, neg_add, zpow_add₀ (pow_ne_zero _ hq)]
    ring

/-- `χ_{q⁻¹}(i, j) χ_q(i, j) = 1` when `π² = 1`. -/
theorem chi_inv_mul_chi (hπ : π ^ 2 = 1) (i j : I) :
    C.chi q⁻¹ π i j * C.chi q π i j = 1 := by
  rw [chi_apply, chi_apply]
  have h1 : ((q⁻¹ ^ (-C.dot i j) : kˣ) : k) * ((q ^ (-C.dot i j) : kˣ) : k) = 1 := by
    rw [← Units.val_mul, inv_zpow', neg_neg, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  calc _ = (((q⁻¹ ^ (-C.dot i j) : kˣ) : k) * ((q ^ (-C.dot i j) : kˣ) : k)) *
        (π ^ 2) ^ (C.parity i * C.parity j).val := by ring
    _ = 1 := by rw [h1, hπ, one_pow, one_mul]

end Field

/-! ### The coefficients -/

/-- The sign `(-1)^{|i||j|} = (-1)^{p i p j}`. -/
lemma neg_one_pow_val_eq_superSign {K : Type*} [Field K] (i j : I) :
    (-1 : K) ^ (C.parity i * C.parity j).val = superSign K C.parity i j := by
  unfold superSign
  generalize C.parity i = a
  generalize C.parity j = b
  fin_cases a <;> fin_cases b <;> simp [show ZMod.val (1 : ZMod 2) = 1 from rfl]

/-- The Laurent polynomial `cᵢ(μ) = ∏ₖ ((-1)^{|i||k|})^{μₖ} [nᵢ - ⟨μ, αᵢ^∨⟩]_{T^{dᵢ}}`. -/
def superCoeff (n : I → ℕ) (i : I) (μ : I →₀ ℕ) : LaurentPolynomial ℚ :=
  algebraMap ℚ (LaurentPolynomial ℚ) (weightSign (superSign ℚ C.parity i) μ) *
    vermaCoeff C.lusztigDatum (fun i ↦ (n i : ℤ)) i μ

variable [Field k] [CharZero k]

lemma map_weightSign_superSign (i : I) (μ : I →₀ ℕ) :
    algebraMap ℚ k (weightSign (superSign ℚ C.parity i) μ) =
      weightSign (superSign k C.parity i) μ := by
  simp only [weightSign, map_finsuppProd, map_pow]
  refine Finsupp.prod_congr fun j _ ↦ ?_
  unfold superSign
  split_ifs <;> simp

lemma evalAt_algebraMap (v : k) (hv : v ≠ 0) (r : ℚ) :
    evalAt v hv (algebraMap ℚ (LaurentPolynomial ℚ) r) = algebraMap ℚ k r := by
  rw [evalAt, show algebraMap ℚ (LaurentPolynomial ℚ) r = LaurentPolynomial.C r from rfl,
    LaurentPolynomial.eval₂_C]

/-- At `T = 1` the coefficients are the classical ones twisted by the super sign character. -/
theorem evalAt_one_superCoeff (n : I → ℕ) (i : I) (μ : I →₀ ℕ) :
    evalAt (1 : ℚ) one_ne_zero (C.superCoeff n i μ) =
      weightSign (superSign ℚ C.parity i) μ * classicalCoeff ℚ C.lusztigDatum n i μ := by
  rw [superCoeff, map_mul, evalAt_algebraMap, evalAt_one_vermaCoeff, classicalCoeff]
  rfl

variable (q : kˣ) (n : I → ℕ)

/-- The scalar `aᵢ = -qᵢ^{-nᵢ}/(qᵢ - qᵢ⁻¹)`. -/
def raiseA (i : I) : k :=
  -(qDenom C.lusztigDatum (q : k) i)⁻¹ * ((q : k) ^ C.d i) ^ (-(n i : ℤ))

/-- The scalar `bᵢ = -qᵢ^{nᵢ}/(qᵢ - qᵢ⁻¹)`. -/
def raiseB (i : I) : k :=
  -(qDenom C.lusztigDatum (q : k) i)⁻¹ * ((q : k) ^ C.d i) ^ (n i : ℤ)

/-- **The coefficients of the raising operators at `π = -1`** are the images of the `cᵢ(μ)` under
`T ↦ q`, when `qᵢ ≠ qᵢ⁻¹`. -/
theorem raiseCoeff_eq_evalAt {i : I} (hi : qDenom C.lusztigDatum (q : k) i ≠ 0) (μ : I →₀ ℕ) :
    C.raiseA q n i * (C.chi q⁻¹ (-1)).wt (Finsupp.single i 1) μ -
        C.raiseB q n i * (C.chi q (-1)).wt (Finsupp.single i 1) μ =
      evalAt (q : k) q.ne_zero (C.superCoeff n i μ) := by
  have hq : (q : k) ≠ 0 := q.ne_zero
  have hx : (q : k) ^ C.d i ≠ 0 := pow_ne_zero _ hq
  rw [superCoeff, map_mul, evalAt_algebraMap, map_weightSign_superSign, evalAt_vermaCoeff _ hq hi,
    chi_wt_single, chi_wt_single, lusztigDatum_d]
  have hs : weightSign (fun j ↦ (-1 : k) ^ (C.parity i * C.parity j).val) μ =
      weightSign (superSign k C.parity i) μ := by
    congr 1; funext j; exact C.neg_one_pow_val_eq_superSign i j
  rw [hs, Units.val_inv_eq_inv_val, inv_pow, inv_zpow', neg_neg, raiseA, raiseB]
  simp only [qDenom, lusztigDatum_d]
  set c := C.lusztigDatum.coPairing i μ
  set x := (q : k) ^ C.d i
  rw [zpow_sub₀ hx, zpow_neg, zpow_neg, zpow_neg, zpow_sub₀ hx]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- `(θᵢ, θᵢ) = (1 - πᵢ qᵢ²)⁻¹` is a unit at `π = ±1` for `q` transcendental over `ℚ`. -/
theorem norm_isUnit_of_transcendental (hq : Transcendental ℚ (q : k)) {π : k} (hπ : π ^ 2 = 1)
    (i : I) : IsUnit (C.norm q π i) := by
  rw [norm, Ring.inverse_eq_inv', isUnit_iff_ne_zero, ne_eq, inv_eq_zero, sub_eq_zero]
  intro h
  have hd := C.d_pos i
  have hp : C.pii π i ^ 2 = 1 := by rw [pii, ← pow_mul, mul_comm, pow_mul, hπ, one_pow]
  have h4 : ((q : k)) ^ (4 * C.d i) = 1 := by
    have : ((C.qi q i : kˣ) : k) = (q : k) ^ C.d i := by simp [qi]
    rw [this] at h
    calc (q : k) ^ (4 * C.d i) = (C.pii π i * ((q : k) ^ C.d i) ^ 2) ^ 2 := by
          rw [mul_pow, hp, one_mul, ← pow_mul, ← pow_mul]; ring_nf
      _ = 1 := by rw [← h, one_pow]
  exact pow_ne_one_of_transcendental hq (by omega) h4

end OddMath.CoveringQuantum.SuperCartanDatum

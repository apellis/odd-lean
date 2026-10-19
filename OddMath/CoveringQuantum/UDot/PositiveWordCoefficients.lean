import OddMath.CoveringQuantum.UDot.PositiveWordForm
import OddMath.CoveringQuantum.PreF.DotSeries
import OddMath.CoveringQuantum.Coefficients.Splitting
import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent coefficients of the positive modified form

Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, Claim 1: expansion of the
existing equal-length positive-word form as guarded Laurent coefficients.
Only π is specialized. The rational-function variable embeds in formal Laurent
series; no numerical evaluation of q or extension of bar to arbitrary series
is used. The form is evaluated in the covering ring before expanding its value.

The source-to-target permutation uses source colours for crossings and target
colours for dots. The physical words are reversed in the form's arguments.
Finite colours and bar consistency remain restrictions of the constructed form.
This is not the unequal-length or arbitrary geometric-choice comparison.
-/

noncomputable section
open scoped BigOperators LaurentSeries RatFunc
namespace OddMath.CoveringQuantum

/-- Specialize π to a rational square root of one, then expand the formal variable.
Each sign alone forgets one component of the covering coefficient ring. -/
def signLaurent (σ : ℚ) (hσ : σ ^ 2 = 1) :
    Coefficients.Ring →+* LaurentSeries ℚ :=
  (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp
    (Coefficients.specialize (RatFunc.C σ)
      (by simp only [← map_pow, hσ, map_one])).toRingHom

@[simp] theorem signLaurent_pi (σ : ℚ) (hσ : σ ^ 2 = 1) :
    signLaurent σ hσ Coefficients.pi = HahnSeries.C σ := by
  simp only [signLaurent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Coefficients.specialize_pi]
  exact RingHom.congr_fun (Subsingleton.elim
    ((algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp RatFunc.C) HahnSeries.C) σ

@[simp] theorem signLaurent_q (σ : ℚ) (hσ : σ ^ 2 = 1) :
    signLaurent σ hσ (Coefficients.q : Coefficients.Ring) = HahnSeries.single 1 1 := by
  change algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
    (Coefficients.specialize _ _ (Coefficients.q : Coefficients.Ring)) = _
  rw [Coefficients.specialize_q]
  exact RatFunc.coe_X

private theorem signLaurent_q_zpow (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    signLaurent σ hσ ((Coefficients.q ^ z : Coefficients.Ringˣ) : Coefficients.Ring) =
      HahnSeries.single z 1 := by
  change ((Units.map (signLaurent σ hσ).toMonoidHom (Coefficients.q ^ z) :
    (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  change (signLaurent σ hσ (Coefficients.q : Coefficients.Ring)) ^ z = _
  rw [signLaurent_q, ← RatFunc.single_zpow]

private theorem signLaurent_norm {I : Type*} (C : SuperCartanDatum I)
    (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) :
    signLaurent σ hσ (C.norm Coefficients.q Coefficients.pi i) =
      (PreF.DotSeries.factor (C.pii σ i) (2 * C.d i)
        (Nat.ne_of_gt (by have := C.d_pos i; omega)) : LaurentSeries ℚ) := by
  let d : LaurentSeries ℚ := 1 - HahnSeries.C (C.pii σ i) * HahnSeries.single 1 1 ^ (2 * C.d i)
  have hn : d * signLaurent σ hσ (C.norm Coefficients.q Coefficients.pi i) = 1 := by
    have h := congrArg (signLaurent σ hσ) (Coefficients.denominator_mul_norm C i)
    simpa only [d, SuperCartanDatum.pii, SuperCartanDatum.qi,
      Units.val_pow_eq_pow_val, map_mul, map_sub, map_pow, map_one,
      signLaurent_pi, signLaurent_q, ← pow_mul, Nat.mul_comm] using h
  have hf : (PreF.DotSeries.factor (C.pii σ i) (2 * C.d i)
      (Nat.ne_of_gt (by have := C.d_pos i; omega)) : LaurentSeries ℚ) * d = 1 := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
      (PreF.DotSeries.factor_mul (C.pii σ i) (2 * C.d i)
        (Nat.ne_of_gt (by have := C.d_pos i; omega)))
    simpa only [d, map_mul, map_sub, map_pow, map_one, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X] using h
  exact (left_inv_eq_right_inv hf hn).symm

private theorem signLaurent_chi {I : Type*} (C : SuperCartanDatum I)
    (σ : ℚ) (hσ : σ ^ 2 = 1) (i j : I) :
    signLaurent σ hσ (C.chi Coefficients.q Coefficients.pi i j) =
      HahnSeries.single (-C.dot i j) (σ ^ (C.parity i * C.parity j).val) := by
  rw [SuperCartanDatum.chi_apply, map_mul, map_pow, signLaurent_q_zpow, signLaurent_pi,
    ← map_pow]
  change HahnSeries.single (-C.dot i j) 1 * HahnSeries.single 0 _ = _
  rw [HahnSeries.single_mul_single, add_zero, one_mul]

private theorem prod_single_parity {J : Type*} (s : Finset J) (k : J → ℤ)
    (p : J → ZMod 2) (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (∏ j ∈ s, (HahnSeries.single (k j) (σ ^ (p j).val) : LaurentSeries ℚ)) =
      HahnSeries.single (∑ j ∈ s, k j) (σ ^ (∑ j ∈ s, p j).val) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, ih,
      HahnSeries.single_mul_single]
    congr 1
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hσ, pow_add]

private theorem signLaurent_crossings {I : Type*} (C : SuperCartanDatum I)
    (σ : ℚ) (hσ : σ ^ 2 = 1) {n : ℕ} (a : Fin n → I) (w : Equiv.Perm (Fin n)) :
    signLaurent σ hσ (∏ r, ∏ s with r < s ∧ w s < w r,
      C.chi Coefficients.q Coefficients.pi (a r) (a s)) =
    HahnSeries.single (∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s))
      (σ ^ (∑ r, ∑ s with r < s ∧ w s < w r, C.parity (a r) * C.parity (a s)).val) := by
  simp only [map_prod, signLaurent_chi]
  simp_rw [prod_single_parity _ _ _ σ hσ]

private theorem signLaurent_norms {I : Type*} (C : SuperCartanDatum I)
    (σ : ℚ) (hσ : σ ^ 2 = 1) {n : ℕ} (a : Fin n → I) :
    signLaurent σ hσ (∏ r, C.norm Coefficients.q Coefficients.pi (a r)) =
      (C.dotSeries σ a : LaurentSeries ℚ) := by
  simp only [map_prod, signLaurent_norm, SuperCartanDatum.dotSeries, PreF.DotSeries.strands]

private theorem shifted_series_coeff (f : PowerSeries ℚ) (k z : ℤ) (c : ℚ) :
    ((HahnSeries.single k c : LaurentSeries ℚ) * (f : LaurentSeries ℚ)).coeff z =
      if k ≤ z then c * PowerSeries.coeff (z - k).toNat f else 0 := by
  rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe]
  by_cases h : k ≤ z
  · rw [ite_eq_right (by omega), ite_eq_left h]
    have he : (z - k).natAbs = (z - k).toNat := by omega
    rw [he]
  · rw [ite_eq_left (by omega), ite_eq_right h, mul_zero]

namespace UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  [Finite I] (Q : RootDatum I X) (hQ : Q.toSuperCartanDatum.BarConsistent)

/-- The Laurent coefficient of the existing positive modified form, for either π sign.
Negative crossing shifts are kept as integers; the guard precedes `toNat`. The
finite-colour and bar-consistency assumptions are inherited from the form. -/
theorem sesquilinearForm_positive_words_coeff
    (σ : ℚ) (hσ : σ ^ 2 = 1) (μ : X) (n : ℕ)
    (a b : Fin n → I) (z : ℤ) :
    let C := Q.toSuperCartanDatum
    let κ : Equiv.Perm (Fin n) → ℤ := fun w =>
      ∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s)
    let ε : Equiv.Perm (Fin n) → ZMod 2 := fun w =>
      ∑ r, ∑ s with r < s ∧ w s < w r,
        Q.parity (a r) * Q.parity (a s)
    (signLaurent σ hσ (sesquilinearForm Q hQ
      (positiveHalf Q Coefficients.q pi μ
        (Q.toSerreF Coefficients.q pi
          (monomial Coefficients.Ring (List.ofFn a).reverse)))
      (positiveHalf Q Coefficients.q pi μ
        (Q.toSerreF Coefficients.q pi
          (monomial Coefficients.Ring (List.ofFn b).reverse))))).coeff z =
      ∑ w : Equiv.Perm (Fin n), if ∀ r, a r = b (w r) then
        if κ w ≤ z then σ ^ (ε w).val *
          PowerSeries.coeff (z - κ w).toNat (C.dotSeries σ b)
        else 0
      else 0 := by
  classical
  dsimp only
  rw [sesquilinearForm_positive_words_permutations]
  simp only [map_mul, map_sum, apply_ite, map_zero, Finset.mul_sum,
    HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : ∀ r, a r = b (w r)
  · rw [ite_eq_left hw, ite_eq_left hw, signLaurent_norms, signLaurent_crossings, mul_comm]
    have hd : Q.toSuperCartanDatum.dotSeries σ a = Q.toSuperCartanDatum.dotSeries σ b := by
      have ha : a = b ∘ w := funext hw
      rw [ha]
      simp only [SuperCartanDatum.dotSeries, PreF.DotSeries.strands]
      exact Equiv.prod_comp w (fun r => DotSeries.factor (Q.pii σ (b r))
        (2 * Q.d (b r)) (Nat.ne_of_gt (by have := Q.d_pos (b r); omega)))
    rw [hd, shifted_series_coeff]
  · simp only [ite_eq_right hw, mul_zero, HahnSeries.coeff_zero]

end UDot.GenericTensor

end OddMath.CoveringQuantum

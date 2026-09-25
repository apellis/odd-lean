import OddMath.Frontier.ElementaryGeneration
import OddMath.Frontier.PbwEquivalence
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Helper for the all-rank center theorem: absence of zero divisors and the
first-variable root relation

EKL arXiv:1111.1320v1, Prop. 2.15, p. 13.

* `mul_ne_zero'`: the skew polynomial ring has no zero divisors (lexicographic
  leading terms multiply, up to a sign `±1`).
* `rootRelation`: for `N = n + 2`, the first variable satisfies the LEFT relation
  `∑_{r=0}^{N} c_r · e_r · x₀^{N-r} = 0`, where `e_r` are the literal elementary
  sums in the tilde generators and `c_0 = 1`, `c_{k+1} = -(-1)^k c_k`.
* `commutes_first_generator`: an element of the kernel commuting with every
  element of the kernel commutes with `x₀`.
-/

namespace OddMath.Frontier.CenterONHRoot
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.ElementaryGeneration OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.FiniteCompleteElementary OddMath.Frontier.PlacticEvaluation
open scoped BigOperators
noncomputable section

/-! ## No zero divisors -/

theorem skewSign_ne_zero {n : ℕ} (a b : Fin n → ℕ) : OddMath.skewSign a b ≠ 0 := by
  unfold OddMath.skewSign
  exact pow_ne_zero _ (by norm_num)

theorem exists_leading {n : ℕ} (f : SkewPolynomial n) (hf : f ≠ 0) :
    ∃ a c, c ≠ 0 ∧ Leading f a c := by
  classical
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨a, ha, hmax⟩ := f.support.exists_max_image (fun b => toLex b) hs
  exact ⟨a, f a, Finsupp.mem_support_iff.mp ha,
    fun b hb => hmax b (Finsupp.mem_support_iff.mpr hb), rfl⟩

theorem mul_ne_zero' {n : ℕ} {f g : SkewPolynomial n} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  obtain ⟨a, c, hc, ha⟩ := exists_leading f hf
  obtain ⟨b, d, hd, hb⟩ := exists_leading g hg
  have h := (leading_mul ha hb).2
  intro h0
  rw [h0] at h
  exact mul_ne_zero (mul_ne_zero hc hd) (skewSign_ne_zero a b) h.symm

theorem eq_zero_of_mul_eq_zero_left {n : ℕ} {p d : SkewPolynomial n} (hp : p ≠ 0)
    (h : p * d = 0) : d = 0 := by
  by_contra hd
  exact mul_ne_zero' hp hd h

/-! ## Strict word sums in an arbitrary ring -/

section Words
variable {R : Type*} [Ring R]

theorem strictSum_vanish : ∀ {m : ℕ} (x : Fin m → R) (k : ℕ), m < k →
    FiniteWords.strictSum x k = 0
  | 0, x, k, h => by
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact FiniteWords.strictSum_empty x k
  | m+1, x, k, h => by
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [FiniteWords.strictSum_succ, strictSum_vanish _ k (by omega),
        strictSum_vanish _ (k+1) (by omega), mul_zero, add_zero]

theorem strictSum_zero_family : ∀ {m : ℕ} (k : ℕ),
    FiniteWords.strictSum (fun _ : Fin m => (0 : R)) k = if k = 0 then 1 else 0
  | 0, 0 => by simp
  | 0, k+1 => by simp
  | m+1, 0 => by simp
  | m+1, k+1 => by
      rw [FiniteWords.strictSum_succ, zero_mul, zero_add]
      exact strictSum_zero_family (m := m) (k+1)

/-- A ring element anticommuting with every letter passes a strict `k`-word sum
with sign `(-1)^k`. -/
theorem strictSum_anticomm (a : R) : ∀ {m : ℕ} (x : Fin m → R),
    (∀ j, a * x j = -(x j * a)) → ∀ k : ℕ,
      a * FiniteWords.strictSum x k = ((-1 : ℤ) ^ k) • (FiniteWords.strictSum x k * a)
  | 0, x, _, 0 => by simp
  | 0, x, _, k+1 => by simp
  | m+1, x, _, 0 => by simp
  | m+1, x, hx, k+1 => by
      have ih1 := strictSum_anticomm a (fun i : Fin m => x i.succ) (fun j => hx j.succ) k
      have ih2 := strictSum_anticomm a (fun i : Fin m => x i.succ) (fun j => hx j.succ) (k+1)
      rw [FiniteWords.strictSum_succ, mul_add, ← mul_assoc, hx 0, neg_mul, mul_assoc, ih1, ih2]
      simp only [mul_smul_comm, pow_succ, mul_smul, neg_one_smul, smul_neg, smul_add, add_mul,
        mul_assoc]
      try abel

end Words

theorem map_strictSum {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) :
    ∀ {m : ℕ} (x : Fin m → R) (k : ℕ),
      φ (FiniteWords.strictSum x k) = FiniteWords.strictSum (fun j => φ (x j)) k
  | 0, x, 0 => by simp
  | 0, x, k+1 => by simp
  | m+1, x, 0 => by simp
  | m+1, x, k+1 => by
      rw [FiniteWords.strictSum_succ, FiniteWords.strictSum_succ, map_add, map_mul,
        map_strictSum φ _ k, map_strictSum φ _ (k+1)]

/-! ## The coefficients and the root relation -/

/-- `c_0 = 1`, `c_{k+1} = -(-1)^k c_k`. -/
def coeff : ℕ → ℤ
  | 0 => 1
  | k+1 => -((-1) ^ k * coeff k)

theorem coeff_cancel (k : ℕ) : coeff k + coeff (k+1) * (-1) ^ k = 0 := by
  have hs : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  simp only [coeff]
  rw [neg_mul, mul_comm ((-1 : ℤ) ^ k * coeff k), ← mul_assoc, hs, one_mul, add_neg_cancel]

theorem tilde_zero {m : ℕ} : tildeGenerator (0 : Fin (m+1)) = generator 0 := by
  simp [tildeGenerator]

/-- The first variable anticommutes with every later tilde generator. -/
theorem first_anticomm {m : ℕ} (j : Fin m) :
    (generator (0 : Fin (m+1)) : SkewPolynomial (m+1)) * tildeGenerator j.succ =
      -(tildeGenerator j.succ * generator 0) := by
  rw [← tilde_zero]
  exact tilde_anticommute _ _ (Fin.succ_ne_zero j).symm

/-- Partial sums of the root relation. -/
theorem partial_root {m : ℕ} (k : ℕ) :
    ∑ r ∈ Finset.range (k+1), coeff r •
        (FiniteWords.strictSum (tildeGenerator (n := m+1)) r *
          (generator (0 : Fin (m+1)) : SkewPolynomial (m+1)) ^ (k - r)) =
      coeff k • FiniteWords.strictSum (fun j : Fin m => tildeGenerator j.succ) k := by
  induction k with
  | zero => simp [coeff]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hshift : ∑ r ∈ Finset.range (k+1), coeff r •
        (FiniteWords.strictSum (tildeGenerator (n := m+1)) r *
          (generator (0 : Fin (m+1)) : SkewPolynomial (m+1)) ^ (k + 1 - r)) =
        (∑ r ∈ Finset.range (k+1), coeff r •
          (FiniteWords.strictSum (tildeGenerator (n := m+1)) r *
            (generator (0 : Fin (m+1)) : SkewPolynomial (m+1)) ^ (k - r))) *
          generator 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : k + 1 - r = (k - r) + 1 := by
        have := Finset.mem_range.mp hr; omega
      rw [hr', pow_succ, smul_mul_assoc, mul_assoc]
    rw [hshift, ih, Nat.sub_self, pow_zero, mul_one, FiniteWords.strictSum_succ, tilde_zero]
    have ha := strictSum_anticomm (generator (0 : Fin (m+1)) : SkewPolynomial (m+1))
      (fun j : Fin m => tildeGenerator j.succ) first_anticomm k
    rw [ha, smul_add, smul_mul_assoc, smul_smul, ← add_assoc, ← add_smul, coeff_cancel,
      zero_smul, zero_add]

/-- The left root relation of the first variable, `N = n + 2`. -/
theorem rootRelation (n : ℕ) :
    ∑ r ∈ Finset.range (n+3), coeff r •
        (elementaryPoly (n+2) r *
          (generator (0 : Fin (n+2)) : SkewPolynomial (n+2)) ^ (n + 2 - r)) = 0 := by
  simp only [elementaryPoly_eq_strictSum]
  rw [partial_root (m := n+1) (n+2), strictSum_vanish _ _ (by omega), smul_zero]

/-! ## A ring map detecting the first variable -/

/-- Free-algebra map `x₀ ↦ X`, `x_j ↦ 0` (`j ≠ 0`). -/
def piFree (m : ℕ) : FreeAlgebra ℤ (Fin (m+1)) →ₐ[ℤ] Polynomial ℤ :=
  FreeAlgebra.lift ℤ (fun j => if j = 0 then Polynomial.X else 0)

theorem piFree_kill (m : ℕ) (w : FreeAlgebra ℤ (Fin (m+1)))
    (hw : w ∈ PbwL2.relIdeal (m+1)) : piFree m w = 0 := by
  rw [PbwL2.relIdeal, PbwL2.relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h =>
      obtain ⟨i, j, hij, rfl⟩ := h
      simp only [map_add, map_mul, piFree, FreeAlgebra.lift_ι_apply]
      by_cases hi : i = 0
      · have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
        simp [hi, hj]
      · simp [hi]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

def piPres (m : ℕ) : PbwL2.Presented (m+1) →+* Polynomial ℤ :=
  Ideal.Quotient.lift (PbwL2.relIdeal (m+1)) (piFree m).toRingHom (piFree_kill m)

def pi (m : ℕ) : SkewPolynomial (m+1) →+* Polynomial ℤ :=
  (piPres m).comp (PbwEquivalence.presentedEquiv (m+1)).symm.toRingHom

theorem pi_generator (m : ℕ) (j : Fin (m+1)) :
    pi m (generator j) = if j = 0 then Polynomial.X else 0 := by
  have he : (PbwEquivalence.presentedEquiv (m+1)).symm (generator j) = PbwL2.q (m+1) j := by
    apply (PbwEquivalence.presentedEquiv (m+1)).injective
    simpa only [RingEquiv.apply_symm_apply, PbwEquivalence.presentedEquiv_apply] using
      (PbwL3.Phi_q (m+1) j).symm
  simp only [pi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he]
  change piFree m (FreeAlgebra.ι ℤ j) = _
  simp [piFree]

theorem pi_tilde_succ (m : ℕ) (j : Fin m) : pi m (tildeGenerator j.succ) = 0 := by
  rw [tildeGenerator, map_zsmul, pi_generator, if_neg (Fin.succ_ne_zero j), smul_zero]

theorem pi_elementary_succ (n k : ℕ) :
    pi (n+1) (elementaryPoly (n+2) (k+1)) = if k = 0 then Polynomial.X else 0 := by
  rw [elementaryPoly_eq_strictSum, FiniteWords.strictSum_succ, map_add, map_mul,
    map_strictSum, map_strictSum, tilde_zero, pi_generator, if_pos rfl]
  simp only [pi_tilde_succ, strictSum_zero_family]
  split <;> simp_all

/-! ## Commuting with `x₀` -/

/-- The parity-dependent factor in `z x₀^m - x₀^m z = W_m · (z x₀ - x₀ z)`. -/
def parityFactor {N : ℕ} (x : SkewPolynomial N) (m : ℕ) : SkewPolynomial N :=
  if Even m then 0 else x ^ (m - 1)

theorem commutator_pow {N : ℕ} (i : Fin N) (z : SkewPolynomial N) (m : ℕ) :
    z * generator i ^ m - generator i ^ m * z =
      parityFactor (generator i) m * (z * generator i - generator i * z) := by
  have hsq : ∀ k : ℕ, (generator i ^ 2) ^ k * z = z * (generator i ^ 2) ^ k := by
    intro k
    exact ((Commute.pow_left (show Commute (generator i ^ 2) z from
      square_comm i z) k)).eq
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [parityFactor, if_pos (even_two_mul k), zero_mul, pow_mul, hsq, sub_self]
  · have hne : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
    rw [parityFactor, if_neg hne, Nat.add_sub_cancel, pow_succ, pow_mul, ← mul_assoc,
      ← hsq, mul_sub, mul_assoc, mul_assoc]

theorem pi_parityFactor (n m : ℕ) :
    pi (n+1) (parityFactor (generator (0 : Fin (n+2))) m) =
      if Even m then 0 else Polynomial.X ^ (m - 1) := by
  unfold parityFactor
  split <;> simp [pi_generator]

/-- The left coefficient polynomial `P = ∑ c_r e_r W_{N-r}`. -/
def leftFactor (n : ℕ) : SkewPolynomial (n+2) :=
  ∑ r ∈ Finset.range (n+3), coeff r •
    (elementaryPoly (n+2) r * parityFactor (generator (0 : Fin (n+2))) (n + 2 - r))

theorem pi_leftFactor (n : ℕ) :
    pi (n+1) (leftFactor n) = if Even n then -(Polynomial.X ^ (n+1)) else Polynomial.X ^ (n+1) := by
  unfold leftFactor
  rw [map_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∀ r ∈ Finset.range (n+1), pi (n+1) (coeff (r+1+1) •
      (elementaryPoly (n+2) (r+1+1) *
        parityFactor (generator (0 : Fin (n+2))) (n + 2 - (r+1+1)))) = 0 := by
    intro r _
    rw [map_zsmul, map_mul, pi_elementary_succ, if_neg (Nat.succ_ne_zero r), zero_mul, smul_zero]
  rw [Finset.sum_eq_zero hrest, zero_add]
  rw [map_zsmul, map_zsmul, map_mul, map_mul, pi_elementary_succ, if_pos rfl,
    pi_parityFactor, pi_parityFactor]
  have h0 : elementaryPoly (n+2) 0 = 1 := by
    rw [elementaryPoly_eq_strictSum, FiniteWords.strictSum_zero]
  rw [h0, map_one, one_mul]
  simp only [coeff, zero_add, Nat.sub_zero, show n + 2 - 1 = n + 1 by omega]
  by_cases hn : Even n
  · have h1 : ¬ Even (n+1) := by simpa [Nat.even_add_one] using hn
    have h2 : Even (n+2) := by simpa [Nat.even_add] using hn
    rw [if_pos h2, if_neg h1, if_pos hn, Nat.add_sub_cancel, ← pow_succ']
    simp
  · have h1 : Even (n+1) := by simpa [Nat.even_add_one] using hn
    have h2 : ¬ Even (n+2) := by simpa [Nat.even_add] using hn
    rw [if_neg h2, if_pos h1, if_neg hn]
    simp

theorem leftFactor_ne_zero (n : ℕ) : leftFactor n ≠ 0 := by
  intro h
  have hp := pi_leftFactor n
  rw [h, map_zero] at hp
  have hX : (Polynomial.X : Polynomial ℤ) ^ (n+1) ≠ 0 := by
    intro h0
    have := congrArg (fun p : Polynomial ℤ => p.coeff (n+1)) h0
    simp at this
  split at hp
  · exact hX (neg_eq_zero.mp hp.symm)
  · exact hX hp.symm

/-- An element of the kernel commuting with every element of the kernel commutes
with the first variable. -/
theorem commutes_first_generator (n : ℕ) (z : SkewPolynomial (n+2))
    (hz : ∀ k ∈ kernelSubring n, k * z = z * k) :
    z * generator 0 = generator 0 * z := by
  set D := z * generator (0 : Fin (n+2)) - generator 0 * z with hD
  have hsum : z * (∑ r ∈ Finset.range (n+3), coeff r •
        (elementaryPoly (n+2) r * (generator (0 : Fin (n+2))) ^ (n + 2 - r))) -
      (∑ r ∈ Finset.range (n+3), coeff r •
        (elementaryPoly (n+2) r * (generator (0 : Fin (n+2))) ^ (n + 2 - r))) * z =
      leftFactor n * D := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, leftFactor, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    have hc := hz _ (elementary_mem n r)
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_mul_assoc]
    congr 1
    rw [← mul_assoc, ← hc, mul_assoc, mul_assoc, mul_assoc, ← mul_sub, commutator_pow]
  rw [rootRelation, mul_zero, zero_mul, sub_zero] at hsum
  have hD0 := eq_zero_of_mul_eq_zero_left (leftFactor_ne_zero n) hsum.symm
  exact sub_eq_zero.mp hD0

end
end OddMath.Frontier.CenterONHRoot

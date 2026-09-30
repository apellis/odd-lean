import OddMath.Frontier.EQPdgExt

/-!
# The block homotopy identity `Σ_{a+c=p-1} D^a T_b D^c = -N_b`

Auxiliary material for Ellis–Qi, arXiv:1504.01712v2, Appendix A.4.2.

Over a field `𝕜` of characteristic `p`, with `D = d - (n-1) e_1` on `𝕜[x_1, …, x_n]`
(`dAlt`, `D(x^β) = Σ_i (β_i - (n-1)) x^{β + e_i}`) and a block `[b, b + p)` of exponents with
`b ≡ n (mod p)`:

* `blockT b`: `x^β ↦ Σ_{i : β_i = b+p-1} x^{β with β_i := b}` (the sum over `i` of the
  one-variable operator `t^{b+p-1} ↦ t^b`),
* `blockN b`: `x^β ↦ #{i : b ≤ β_i < b + p} · x^β`,

and `sum_dAlt_pow_blockT` is the identity `Σ_{a+c=p-1} D^a T_b D^c = -N_b`.
-/

namespace OddMath.Frontier.EQPdg

open Finset

noncomputable section

section Uni

open Polynomial

variable {k : Type*} [Field k] (n : ℕ)

/-- One-variable version of `D`: `t^a ↦ (a - (n-1)) t^{a+1}`. -/
def dOne : Module.End k (Polynomial k) :=
  LinearMap.mulLeft k ((X : Polynomial k) ^ 2) ∘ₗ derivative -
    ((n : k) - 1) • LinearMap.mulLeft k (X : Polynomial k)

theorem dOne_X_pow (a : ℕ) :
    dOne (k := k) n (X ^ a) = (((a : ℕ) : k) - ((n : k) - 1)) • (X : Polynomial k) ^ (a + 1) := by
  simp only [dOne, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
  rw [derivative_X_pow]
  rcases a with _ | a
  · simp only [Nat.cast_zero, map_zero, zero_mul, mul_zero, zero_sub, map_neg, map_sub,
      map_natCast, map_one]
    ring
  · simp only [Nat.add_sub_cancel, map_sub, map_natCast, map_one]
    push_cast
    ring

/-- The weight `Π_{t<i} (c + t - (n-1))` of `D^i(t^c)`. -/
def wt (c i : ℕ) : k := ∏ t ∈ range i, (((c + t : ℕ) : k) - ((n : k) - 1))

theorem dOne_pow_X_pow (c i : ℕ) :
    ((dOne (k := k) n) ^ i) (X ^ c) = wt (k := k) n c i • (X : Polynomial k) ^ (c + i) := by
  induction i with
  | zero => simp [wt]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, dOne_X_pow, smul_smul, wt, wt,
      Finset.prod_range_succ, mul_comm, add_assoc]

variable (p : ℕ)

theorem wt_add (c i j : ℕ) : wt (k := k) n c (i + j) = wt (k := k) n c i * wt (k := k) n (c + i) j := by
  rw [wt, wt, wt, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [add_assoc]

/-- One-variable `T_b`: `t^{b+p-1} ↦ t^b`, other monomials `↦ 0`. -/
def tOne (b : ℕ) : Module.End k (Polynomial k) :=
  (lcoeff k (b + p - 1)).smulRight ((X : Polynomial k) ^ b)

/-- One-variable `N_b`: the projection onto the span of `t^c`, `b ≤ c < b + p`. -/
def pOne (b : ℕ) : Module.End k (Polynomial k) :=
  ∑ c ∈ Ico b (b + p), (lcoeff k c).smulRight ((X : Polynomial k) ^ c)

theorem tOne_X_pow (b c : ℕ) :
    tOne (k := k) p b (X ^ c) = if c = b + p - 1 then (X : Polynomial k) ^ b else 0 := by
  simp only [tOne, LinearMap.smulRight_apply, lcoeff_apply, coeff_X_pow]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem pOne_X_pow (b c : ℕ) :
    pOne (k := k) p b (X ^ c) = if c ∈ Ico b (b + p) then (X : Polynomial k) ^ c else 0 := by
  simp only [pOne, LinearMap.sum_apply, LinearMap.smulRight_apply, lcoeff_apply, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd; simp [hd]
    · intro h'; exact absurd h h'
  · refine Finset.sum_eq_zero fun d hd => ?_
    have : d ≠ c := fun e => h (e ▸ hd)
    simp [this]

variable [hp : Fact p.Prime] [CharP k p]

theorem factorial_pred_cast : (((p - 1).factorial : ℕ) : k) = -1 := by
  have h := ZMod.wilsons_lemma (p := p)
  have := congrArg (ZMod.castHom (dvd_refl p) k) h
  rwa [map_natCast, map_neg, map_one] at this

theorem wt_block {b : ℕ} (hb : (b : k) = n) : wt (k := k) n b (p - 1) = -1 := by
  rw [wt, ← factorial_pred_cast (k := k) p, ← Finset.prod_range_add_one_eq_factorial,
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun t _ => ?_
  push_cast
  rw [hb]
  ring

/-- **One-variable identity**: `Σ_{a+c=p-1} D^a T_b D^c = -N_b` on `𝕜[t]` when `b ≡ n`. -/
theorem sum_dOne_pow_tOne {b : ℕ} (hb : (b : k) = n) :
    ∑ a ∈ range p, (dOne (k := k) n) ^ a * tOne p b * (dOne n) ^ (p - 1 - a) = -pOne p b := by
  have hp2 := hp.out.two_le
  refine (Polynomial.basisMonomials k).ext fun c => ?_
  simp only [Polynomial.coe_basisMonomials]
  rw [monomial_one_right_eq_X_pow, LinearMap.sum_apply,
    LinearMap.neg_apply, pOne_X_pow]
  have key : ∀ a ∈ range p, (((dOne (k := k) n) ^ a * tOne p b * (dOne n) ^ (p - 1 - a) :
      Module.End k (Polynomial k)) (X ^ c)) =
      if c = b + a then (wt (k := k) n c (p - 1 - a) * wt (k := k) n b a) • (X : Polynomial k) ^ c
      else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    rw [Module.End.mul_apply, Module.End.mul_apply, dOne_pow_X_pow, map_smul, tOne_X_pow]
    by_cases h : c = b + a
    · have h' : c + (p - 1 - a) = b + p - 1 := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h), map_smul,
        dOne_pow_X_pow, smul_smul, h]
    · have h' : ¬ c + (p - 1 - a) = b + p - 1 := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h), smul_zero,
        map_zero]
  rw [Finset.sum_congr rfl key]
  by_cases hc : c ∈ Ico b (b + p)
  · have hc' := Finset.mem_Ico.mp hc
    simp only [hc, ↓reduceIte]
    rw [Finset.sum_eq_single (c - b)]
    · have h1 : c = b + (c - b) := by omega
      simp only [← h1, ↓reduceIte]
      have hsplit : wt (k := k) n b (p - 1) =
          wt (k := k) n b (c - b) * wt (k := k) n c (p - 1 - (c - b)) := by
        rw [show p - 1 = (c - b) + (p - 1 - (c - b)) by omega, wt_add, ← h1]
        congr 2
        omega
      rw [mul_comm, ← hsplit, wt_block n p hb, neg_one_smul]
    · intro a _ ha
      have : ¬ c = b + a := by omega
      simp only [this, ↓reduceIte]
    · intro h; exfalso; apply h; rw [Finset.mem_range]; omega
  · simp only [hc, ↓reduceIte, neg_zero]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_range] at ha
    have : ¬ c = b + a := by
      intro h; apply hc; rw [Finset.mem_Ico]; omega
    simp only [this, ↓reduceIte]

end Uni

section Multi

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

theorem dAlt_eq_sum_extOp :
    (dAlt : Module.End k (MvPolynomial (Fin n) k)) = ∑ j, extOp j (dOne n) := by
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  simp only [coe_basisMonomials]
  rw [LinearMap.sum_apply]
  have hβ : (monomial β 1 : MvPolynomial (Fin n) k) = xpow ⇑β := by
    rw [xpow_eq_monomial,
      show Finsupp.equivFunOnFinite.symm ⇑β = β from Finsupp.equivFunOnFinite.symm_apply_apply β]
  rw [hβ, dAlt_xpow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hβ, extOp_monomial, one_smul, dOne_X_pow, map_smul, mul_smul_comm,
    Polynomial.aeval_X_pow, xpow_eq_monomial]
  congr 1
  rw [pow_succ, ← mul_assoc, show (monomial (Finsupp.erase j β) 1 * X j ^ β j :
      MvPolynomial (Fin n) k) = monomial β 1 by
    rw [monomial_eq_erase_mul β j, Polynomial.aeval_X_pow]]
  rw [show (X j : MvPolynomial (Fin n) k) = monomial (Finsupp.single j 1) 1 from rfl,
    monomial_mul_monomial, mul_one]
  rw [show Finsupp.equivFunOnFinite.symm (⇑β + Pi.single j 1) = β + Finsupp.single j 1 from ?_]
  ext i
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

variable (p : ℕ)

/-- `T_b = Σ_j (t^{b+p-1} ↦ t^b)` in the variable `x_j`. -/
def blockT (b : ℕ) : Module.End k (MvPolynomial (Fin n) k) := ∑ j, extOp j (tOne p b)

/-- `N_b(x^β) = #{j : b ≤ β_j < b + p} · x^β`. -/
def blockN (b : ℕ) : Module.End k (MvPolynomial (Fin n) k) := ∑ j, extOp j (pOne p b)

theorem blockN_monomial (b : ℕ) (β : Fin n →₀ ℕ) (c : k) :
    blockN p b (monomial β c) =
      ((univ.filter (fun j => β j ∈ Ico b (b + p))).card : k) • monomial β c := by
  rw [blockN, LinearMap.sum_apply]
  have h : ∀ j, extOp j (pOne p b) (monomial β c) =
      if β j ∈ Ico b (b + p) then monomial β c else 0 := by
    intro j
    rw [extOp_monomial, pOne_X_pow]
    split_ifs with h
    · rw [← monomial_eq_erase_mul, smul_monomial, smul_eq_mul, mul_one]
    · simp
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem rename_blockT (σ : Equiv.Perm (Fin n)) (b : ℕ) (f : MvPolynomial (Fin n) k) :
    blockT p b (rename σ f) = rename σ (blockT p b f) :=
  rename_sum_extOp σ _ f

/-- **The block homotopy identity** `Σ_{a+c=p-1} D^a T_b D^c = -N_b` for `b ≡ n (mod p)`. -/
theorem sum_dAlt_pow_blockT [Fact p.Prime] [CharP k p] {b : ℕ} (hb : (b : k) = n) :
    ∑ a ∈ range p, (dAlt : Module.End k (MvPolynomial (Fin n) k)) ^ a * blockT p b *
      dAlt ^ (p - 1 - a) = -blockN p b := by
  rw [sum_pow_mul_pow_eq_ad (k := k) p, blockT, map_sum, blockN, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsplit : (dAlt : Module.End k (MvPolynomial (Fin n) k)) =
      extOp j (dOne n) + ∑ i ∈ univ.erase j, extOp i (dOne n) := by
    rw [dAlt_eq_sum_extOp]
    exact (Finset.add_sum_erase _ (fun i => extOp i (dOne (k := k) n)) (Finset.mem_univ j)).symm
  have hc1 : Commute (extOp j (dOne (k := k) n)) (∑ i ∈ univ.erase j, extOp i (dOne n)) :=
    Commute.sum_right _ _ _ fun i hi => extOp_comm (Finset.ne_of_mem_erase hi).symm _ _
  have hc2 : Commute (extOp j (tOne (k := k) p b)) (∑ i ∈ univ.erase j, extOp i (dOne n)) :=
    Commute.sum_right _ _ _ fun i hi => extOp_comm (Finset.ne_of_mem_erase hi).symm _ _
  rw [hsplit, (adL_add_pow_of_commute _ _ _ hc1 hc2 (p - 1)).1, ← extHom_apply, ← extHom_apply,
    ← algHom_adL_pow, ← sum_pow_mul_pow_eq_ad (k := k) p, sum_dOne_pow_tOne n p hb, map_neg,
    extHom_apply]

end Multi

end

end OddMath.Frontier.EQPdg

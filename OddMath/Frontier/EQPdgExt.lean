import OddMath.Frontier.EQPdgAlt
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.NumberTheory.Wilson
import Mathlib.Algebra.Algebra.Bilinear

/-!
# A contracting homotopy for the p-differential on polynomials

Auxiliary material for Ellis–Qi, arXiv:1504.01712v2, Appendix A.4.2 (the slash cohomology of
symmetric functions).

Over a field `𝕜` of characteristic `p`, consider on `𝕜[x_1, …, x_n]` the operator
`D = d - (n-1) e_1`, `D(x^β) = Σ_i (β_i - (n-1)) x^{β + e_i}` (`dAlt`), which corresponds to the
differential of symmetric polynomials under multiplication by the Vandermonde determinant. For
a *block* of exponents `[b, b + p)` with `b ≡ n (mod p)` let

* `T_b(x^β) = Σ_{i : β_i = b + p - 1} x^{β with β_i := b}` (`blockT`),
* `N_b(x^β) = #{i : β_i ∈ [b, b+p)} · x^β` (`blockN`).

The main result `sum_dAlt_pow_blockT` is the operator identity

  `Σ_{a+c = p-1} D^a T_b D^c = -N_b`,

so `T_b` is a contracting homotopy (up to the scalar `-N_b`) on every subspace on which the
number of exponents in the block is nonzero mod `p`. It is proved from the one-variable identity
(where `(p-1)! = -1` by Wilson's theorem enters) by extending one-variable operators to `n`
variables (`extOp`), and the identity `Σ_{a+c=p-1} X^a Y X^c = ad_X^{p-1}(Y)` in characteristic
`p` (`sum_pow_mul_pow_eq_ad`).
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset

noncomputable section

/-! ## The identity `Σ_{a+c=p-1} X^a Y X^c = ad_X^{p-1}(Y)` in characteristic `p` -/

/-- `ad_X = L_X - R_X` as an endomorphism of `S`. -/
abbrev adL (k : Type*) {S : Type*} [Field k] [Ring S] [Algebra k S] (X : S) : Module.End k S :=
  LinearMap.mulLeft k X - LinearMap.mulRight k X

section CharId

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

theorem choose_pred_cast (i : ℕ) (hi : i ≤ p - 1) :
    (((p - 1).choose i : ℕ) : k) = (-1) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hp2 := hp.out.two_le
    have h1 : p.choose (i + 1) = (p - 1).choose i + (p - 1).choose (i + 1) := by
      conv_lhs => rw [show p = (p - 1) + 1 by omega]
      exact Nat.choose_succ_succ _ _
    have h2 : ((p.choose (i + 1) : ℕ) : k) = 0 :=
      (CharP.cast_eq_zero_iff k p _).mpr (hp.out.dvd_choose_self (by omega) (by omega))
    rw [h1, Nat.cast_add, ih (by omega)] at h2
    rw [pow_succ]
    linear_combination h2

theorem neg_one_pow_pred : (-1 : k) ^ (p - 1) = 1 := by
  have h := neg_one_pow_char k p
  have hp2 := hp.out.two_le
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [hq, pow_succ] at h
  rw [hq, Nat.add_sub_cancel]
  linear_combination (-1 : k) * h

theorem sum_pow_mul_pow_eq_sub_pow {S : Type*} [Ring S] [Algebra k S] {a b : S}
    (hab : Commute a b) :
    ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i) = (a - b) ^ (p - 1) := by
  have hp2 := hp.out.two_le
  rw [sub_eq_add_neg, (hab.neg_right).add_pow, show p - 1 + 1 = p by omega]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ p - 1 := by rw [Finset.mem_range] at hi; omega
  have hC : (((p - 1).choose i : ℕ) : S) = (-1) ^ i := by
    rw [← map_natCast (algebraMap k S), choose_pred_cast p i hi]
    simp
  have hneg : (-1 : S) ^ (p - 1) = 1 := by
    have := congrArg (algebraMap k S) (neg_one_pow_pred (k := k) p)
    simpa using this
  rw [neg_pow, hC, mul_assoc, mul_assoc]
  rw [← ((Commute.neg_one_left (b ^ (p - 1 - i))).pow_left i).eq]
  rw [← mul_assoc ((-1 : S) ^ (p - 1 - i)), ← pow_add, show p - 1 - i + i = p - 1 by omega,
    hneg, one_mul]

/-- In characteristic `p`: `Σ_{a+c=p-1} X^a Y X^c = ad_X^{p-1}(Y)`. -/
theorem sum_pow_mul_pow_eq_ad {S : Type*} [Ring S] [Algebra k S] (X Y : S) :
    ∑ i ∈ range p, X ^ i * Y * X ^ (p - 1 - i) =
      ((adL k X) ^ (p - 1)) Y := by
  rw [← sum_pow_mul_pow_eq_sub_pow (k := k) p (LinearMap.commute_mulLeft_right X X),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp [mul_assoc]

end CharId

section Ad

variable {k : Type*} [Field k] {S S' : Type*} [Ring S] [Algebra k S] [Ring S'] [Algebra k S']

theorem adL_apply (X Y : S) : adL k X Y = X * Y - Y * X := rfl

theorem algHom_adL_pow (φ : S →ₐ[k] S') (X Y : S) (m : ℕ) :
    φ (((adL k X) ^ m) Y) = ((adL k (φ X)) ^ m) (φ Y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, adL_apply, adL_apply,
      ← ih]
    simp

theorem adL_add_pow_of_commute (X E Y : S) (hXE : Commute X E) (hYE : Commute Y E) (m : ℕ) :
    ((adL k (X + E)) ^ m) Y = ((adL k X) ^ m) Y ∧
      Commute (((adL k X) ^ m) Y) E := by
  induction m with
  | zero => simpa using hYE
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pow_succ', Module.End.mul_apply, h1, pow_succ', Module.End.mul_apply, adL_apply,
      adL_apply]
    refine ⟨?_, ?_⟩
    · rw [add_mul, mul_add, h2.eq]; abel
    · exact (hXE.mul_left h2).sub_left (h2.mul_left hXE)

end Ad


/-! ## Extending one-variable operators to `n` variables -/

section Ext

variable {k : Type*} [Field k] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) k

/-- `extOp j A` applies the one-variable operator `A` in the variable `x_j`:
`x^β ↦ x^{β - β_j e_j} · A(t^{β_j})(x_j)`. -/
def extOp (j : Fin n) (A : Module.End k (Polynomial k)) : Module.End k P :=
  (basisMonomials (Fin n) k).constr k
    (fun β => monomial (Finsupp.erase j β) 1 * Polynomial.aeval (X j) (A (Polynomial.X ^ β j)))

theorem extOp_monomial (j : Fin n) (A : Module.End k (Polynomial k)) (β : Fin n →₀ ℕ) (c : k) :
    extOp j A (monomial β c) =
      c • (monomial (Finsupp.erase j β) 1 * Polynomial.aeval (X j) (A (Polynomial.X ^ β j))) := by
  rw [show (monomial β c : P) = c • basisMonomials (Fin n) k β by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, extOp, Module.Basis.constr_basis]

theorem erase_add_single {γ : Fin n →₀ ℕ} {j : Fin n} (hγ : γ j = 0) (m : ℕ) :
    Finsupp.erase j (γ + Finsupp.single j m) = γ := by
  ext i
  rw [Finsupp.erase_apply]
  split_ifs with h
  · subst h; exact hγ.symm
  · simp [Ne.symm h]

theorem monomial_mul_aeval_monomial (γ : Fin n →₀ ℕ) (c a : k) (j : Fin n) (m : ℕ) :
    (monomial γ c * Polynomial.aeval (X j) (Polynomial.monomial m a) : P) =
      monomial (γ + Finsupp.single j m) (c * a) := by
  rw [Polynomial.aeval_monomial, X_pow_eq_monomial, algebraMap_eq, C_mul_monomial,
    monomial_mul_monomial, mul_one]

theorem extOp_mul_aeval (j : Fin n) (A : Module.End k (Polynomial k)) {γ : Fin n →₀ ℕ}
    (hγ : γ j = 0) (c : k) (q : Polynomial k) :
    extOp j A (monomial γ c * Polynomial.aeval (X j) q) =
      monomial γ c * Polynomial.aeval (X j) (A q) := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
  | monomial m a =>
    rw [monomial_mul_aeval_monomial, extOp_monomial, erase_add_single hγ]
    simp only [Finsupp.add_apply, hγ, Finsupp.single_eq_same, zero_add]
    rw [← Polynomial.smul_X_eq_monomial, map_smul, map_smul,
      show (monomial γ c : P) = c • (monomial γ 1 : P) by rw [smul_monomial, smul_eq_mul, mul_one],
      smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extOp_mul_aeval₂ {i j : Fin n} (hij : i ≠ j) (A : Module.End k (Polynomial k))
    {γ : Fin n →₀ ℕ} (hγ : γ i = 0) (c : k) (q' q : Polynomial k) :
    extOp i A (monomial γ c * Polynomial.aeval (X j) q' * Polynomial.aeval (X i) q) =
      monomial γ c * Polynomial.aeval (X j) q' * Polynomial.aeval (X i) (A q) := by
  induction q' using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => simp only [map_add, mul_add, add_mul, h₁, h₂]
  | monomial m a =>
    rw [monomial_mul_aeval_monomial]
    exact extOp_mul_aeval i A (by simp [hij, hγ]) _ q

theorem extOp_mul (j : Fin n) (A B : Module.End k (Polynomial k)) :
    extOp j (A * B) = extOp j A * extOp j B := by
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  rw [coe_basisMonomials, Module.End.mul_apply, extOp_monomial, extOp_monomial, one_smul,
    one_smul, extOp_mul_aeval j A (by simp)]
  rfl

theorem monomial_eq_erase_mul (γ : Fin n →₀ ℕ) (i : Fin n) :
    (monomial γ 1 : P) = monomial (Finsupp.erase i γ) 1 * Polynomial.aeval (X i)
      ((Polynomial.X : Polynomial k) ^ γ i) := by
  rw [Polynomial.aeval_X_pow, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [show Finsupp.erase i γ + Finsupp.single i (γ i) = γ from ?_]
  ext l
  by_cases h : l = i
  · subst h; simp
  · simp [h]

theorem extOp_one (j : Fin n) : extOp j (1 : Module.End k (Polynomial k)) = 1 := by
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  rw [coe_basisMonomials, extOp_monomial, one_smul, Module.End.one_apply, Module.End.one_apply,
    ← monomial_eq_erase_mul]

theorem extOp_add (j : Fin n) (A B : Module.End k (Polynomial k)) :
    extOp j (A + B) = extOp j A + extOp j B := by
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  rw [coe_basisMonomials, LinearMap.add_apply, extOp_monomial, extOp_monomial, extOp_monomial]
  simp [mul_add]

theorem extOp_smul (j : Fin n) (c : k) (A : Module.End k (Polynomial k)) :
    extOp j (c • A) = c • extOp j A := by
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  rw [coe_basisMonomials, LinearMap.smul_apply, extOp_monomial, extOp_monomial]
  simp

/-- `extOp j` as a `𝕜`-algebra homomorphism. -/
def extHom (j : Fin n) : Module.End k (Polynomial k) →ₐ[k] Module.End k P where
  toFun := extOp j
  map_one' := extOp_one j
  map_mul' := extOp_mul j
  map_zero' := by
    have := extOp_smul j (0 : k) 0
    simpa using this
  map_add' := extOp_add j
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, extOp_smul, extOp_one, Algebra.algebraMap_eq_smul_one]

theorem extHom_apply (j : Fin n) (A : Module.End k (Polynomial k)) :
    extHom j A = extOp j A := rfl

theorem erase_erase_comm (β : Fin n →₀ ℕ) (i j : Fin n) :
    Finsupp.erase i (Finsupp.erase j β) = Finsupp.erase j (Finsupp.erase i β) := by
  ext l; simp only [Finsupp.erase_apply]; split_ifs <;> rfl

/-- Operators in different variables commute. -/
theorem extOp_comm {i j : Fin n} (hij : i ≠ j) (A B : Module.End k (Polynomial k)) :
    extOp i A * extOp j B = extOp j B * extOp i A := by
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  rw [coe_basisMonomials, Module.End.mul_apply, Module.End.mul_apply, extOp_monomial,
    extOp_monomial, one_smul, one_smul]
  have hj : (Finsupp.erase j β) i = β i := by simp [hij]
  have hi : (Finsupp.erase i β) j = β j := by simp [Ne.symm hij]
  rw [monomial_eq_erase_mul (Finsupp.erase j β) i, hj,
    mul_right_comm (monomial (Finsupp.erase i (Finsupp.erase j β)) 1),
    extOp_mul_aeval₂ hij A (by simp) 1]
  rw [monomial_eq_erase_mul (Finsupp.erase i β) j, hi,
    mul_right_comm (monomial (Finsupp.erase j (Finsupp.erase i β)) 1),
    extOp_mul_aeval₂ (Ne.symm hij) B (by simp) 1]
  rw [erase_erase_comm, mul_right_comm]

theorem rename_extOp_monomial (σ : Equiv.Perm (Fin n)) (j : Fin n)
    (A : Module.End k (Polynomial k)) (β : Fin n →₀ ℕ) (c : k) :
    rename σ (extOp j A (monomial β c)) = extOp (σ j) A (rename σ (monomial β c)) := by
  rw [extOp_monomial, rename_monomial, extOp_monomial, map_smul, map_mul, rename_monomial,
    ← Polynomial.aeval_algHom_apply, rename_X, Finsupp.mapDomain_apply_of_injective σ.injective]
  rw [show Finsupp.mapDomain σ (Finsupp.erase j β) = Finsupp.erase (σ j) (Finsupp.mapDomain σ β)
    from ?_]
  ext l
  obtain ⟨l', rfl⟩ := σ.surjective l
  simp [Finsupp.erase_apply, Finsupp.mapDomain_apply_of_injective σ.injective]

theorem rename_extOp (σ : Equiv.Perm (Fin n)) (j : Fin n) (A : Module.End k (Polynomial k))
    (f : P) : rename σ (extOp j A f) = extOp (σ j) A (rename σ f) := by
  rw [f.as_sum]
  simp only [map_sum, rename_extOp_monomial]

/-- The sum `Σ_j extOp j A` commutes with permutations of the variables. -/
theorem rename_sum_extOp (σ : Equiv.Perm (Fin n)) (A : Module.End k (Polynomial k)) (f : P) :
    (∑ j, extOp j A) (rename σ f) = rename σ ((∑ j, extOp j A) f) := by
  simp only [LinearMap.sum_apply, map_sum, rename_extOp]
  exact (Equiv.sum_comp σ (fun j => extOp j A (rename σ f))).symm

end Ext

end

end OddMath.Frontier.EQPdg

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The p-differential on polynomials and symmetric polynomials

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2.

On `R[x_1, …, x_n]` (`MvPolynomial σ R`, any commutative ring `R`) let `d` be the derivation with
`d(x_i) = x_i²` (`pd`). This file proves:

* `pd_rename`: `d` commutes with renaming variables; hence symmetric polynomials are `d`-stable
  (`pd_isSymmetric`);
* `pd_pow_X`: `d^m(x_i) = m! x_i^{m+1}`;
* `pd_pow_char`: in characteristic `p` (`p` prime) `d^p = 0`, i.e. `R[x_1, …, x_n]` is a
  p-dg algebra. More generally the `p`-th iterate of a derivation in characteristic `p` is a
  derivation (`iterate_char_leibniz`);
* `pd_esymm`: `d(e_k) = e_1 e_k - (k+1) e_{k+1}`, and `pd_hsymm`:
  `d(h_k) = (k+1) h_{k+1} - h_1 h_k`, for the elementary and complete homogeneous symmetric
  polynomials in any number of variables (where `e_{k+1} = 0` if `k + 1 > n`).

**Misprint.** Ellis–Qi print `d(e_k) = e_1 e_k - e_{k+1}` and `d(h_k) = h_{k+1} - h_1 h_k`
(attributed to Elias–Qi). The coefficient `k + 1` is missing: `pd_esymm_printed_false` and
`pd_hsymm_printed_false` refute the printed formulas (for `e_1` in two variables and `h_1` in one
variable over `ℤ`, and more generally whenever `k·e_{k+1} ≠ 0`, resp. `k·h_{k+1} ≠ 0`). The
corrected formulas agree with the Schur function formula `d(s_λ) = Σ ct(B) s_{λ+B}` of the paper
(for `λ = (1^k)` the added boxes have contents `1` and `-k`).
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset

noncomputable section

section Deriv

variable (σ R : Type*) [CommRing R]

/-- The derivation `d` of `R[x_σ]` with `d(x_i) = x_i²`. -/
def pd : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R (fun i => X i ^ 2)

/-- `d` as a linear endomorphism. -/
abbrev pdL : Module.End R (MvPolynomial σ R) := (pd σ R : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)

variable {σ R}

@[simp] theorem pd_X (i : σ) : pd σ R (X i) = X i ^ 2 := mkDerivation_X _ _ _

@[simp] theorem pd_C (r : R) : pd σ R (C r) = 0 := (pd σ R).map_algebraMap r

theorem pd_monomial [DecidableEq σ] (s : σ →₀ ℕ) (r : R) :
    pd σ R (monomial s r) = ∑ i ∈ s.support, monomial (s + Finsupp.single i 1) (r * s i) := by
  rw [pd, mkDerivation_monomial, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : 1 ≤ s i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hexp : s - Finsupp.single i 1 + Finsupp.single i 2 = s + Finsupp.single i 1 := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  rw [smul_eq_mul, X_pow_eq_monomial, monomial_mul_monomial, smul_eq_C_mul, C_mul_monomial,
    mul_one, hexp]

/-- `d(x^s) = Σ_i s_i x^{s + e_i}` (sum over all variables). -/
theorem pd_monomial' [DecidableEq σ] [Fintype σ] (s : σ →₀ ℕ) (r : R) :
    pd σ R (monomial s r) = ∑ i, monomial (s + Finsupp.single i 1) (r * s i) := by
  rw [pd_monomial]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Finsupp.notMem_support_iff.mp hi]; simp

theorem pd_rename (e : σ ≃ σ) (f : MvPolynomial σ R) :
    rename e (pd σ R f) = pd σ R (rename e f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, map_mul, rename_X, pd_X, map_pow, hf]

theorem pd_isSymmetric {f : MvPolynomial σ R} (hf : f.IsSymmetric) : (pd σ R f).IsSymmetric :=
  fun e => by rw [pd_rename, hf e]

theorem pd_pow_X (m : ℕ) (i : σ) : (pdL σ R ^ m) (X i) = (m.factorial : MvPolynomial σ R) *
    X i ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change pd σ R (_ * _) = _
    rw [Derivation.leibniz, Derivation.leibniz_pow, pd_X]
    have : pd σ R (m.factorial : MvPolynomial σ R) = 0 := by
      rw [← map_natCast (C : R →+* MvPolynomial σ R)]; exact pd_C _
    rw [this, smul_zero, add_zero, Nat.factorial_succ]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.add_sub_cancel]
    ring

end Deriv

section IterateLeibniz

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem iterate_leibniz (D : Derivation R A A) (n : ℕ) (a b : A) :
    ((D : A →ₗ[R] A) ^ n) (a * b) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • (((D : A →ₗ[R] A) ^ ij.1) a *
        ((D : A →ₗ[R] A) ^ ij.2) b) := by
  set L : Module.End R A := (D : A →ₗ[R] A)
  have hL : ∀ x y, L (x * y) = L x * y + x * L y := fun x y => by
    change D (x * y) = D x * y + x * D y
    rw [Derivation.leibniz]; simp [smul_eq_mul]; ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => (L ^ i) a * (L ^ j) b), pow_succ', Module.End.mul_apply, ih, map_sum]
    rw [add_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [map_nsmul, hL, pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      Nat.choose_symm_of_eq_add hij.symm, smul_add]

/-- In characteristic `p`, the `p`-th power of a derivation satisfies the Leibniz rule. -/
theorem iterate_char_leibniz (D : Derivation R A A) (p : ℕ) [hp : Fact p.Prime] [CharP A p]
    (a b : A) : ((D : A →ₗ[R] A) ^ p) (a * b) =
      ((D : A →ₗ[R] A) ^ p) a * b + a * ((D : A →ₗ[R] A) ^ p) b := by
  set L : Module.End R A := (D : A →ₗ[R] A)
  have hp2 := hp.out.two_le
  rw [iterate_leibniz, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∑ i ∈ range q, (q + 1).choose (i + 1) •
      ((L ^ (i + 1)) a * (L ^ (q + 1 - (i + 1))) b) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    have : (((q + 1).choose (i + 1) : ℕ) : A) = 0 :=
      (CharP.cast_eq_zero_iff A (q + 1) _).mpr (hp.out.dvd_choose_self (by omega) (by omega))
    rw [nsmul_eq_mul, this, zero_mul]
  simp only at hmid ⊢
  rw [hmid]
  simp only [Nat.choose_self, Nat.choose_zero_right, one_smul, Nat.sub_self, Nat.sub_zero,
    pow_zero, Module.End.one_apply, zero_add]
  ring

end IterateLeibniz

section CharP

variable {σ R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- **`d^p = 0` in characteristic `p`**: `R[x_σ]` with `d(x_i) = x_i²` is a p-dg algebra. -/
theorem pd_pow_char : pdL σ R ^ p = 0 := by
  have hp := (Fact.out : p.Prime)
  have key : ∀ f : MvPolynomial σ R, (pdL σ R ^ p) f = 0 := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
      rw [hq, pow_succ, Module.End.mul_apply]
      simp [pdL]
    | add f g hf hg => simp [hf, hg]
    | mul_X f i hf =>
      rw [iterate_char_leibniz, hf, pd_pow_X]
      have : ((p.factorial : ℕ) : MvPolynomial σ R) = 0 :=
        (CharP.cast_eq_zero_iff (MvPolynomial σ R) p _).mpr (Nat.dvd_factorial hp.pos le_rfl)
      rw [this]
      ring
  exact LinearMap.ext key

end CharP

/-! ## Elementary symmetric polynomials -/

section Elementary

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
theorem pd_prod_X (t : Finset σ) :
    pd σ R (∏ i ∈ t, X i) = (∑ i ∈ t, X i) * ∏ i ∈ t, X i := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat, Derivation.leibniz, ih, pd_X]
    simp only [smul_eq_mul]
    ring

/-- Double counting: pairs `(t, i)` with `#t = k`, `i ∉ t` versus pairs `(u, i)` with
`#u = k + 1`, `i ∈ u`. -/
theorem sum_powersetCard_insert {M : Type*} [AddCommMonoid M] (k : ℕ) (g : Finset σ → M) :
    ∑ t ∈ powersetCard k univ, ∑ i ∈ univ \ t, g (insert i t) =
      (k + 1) • ∑ u ∈ powersetCard (k + 1) univ, g u := by
  have h1 : ∀ t : Finset σ, ∑ i ∈ univ \ t, g (insert i t) =
      ∑ i, if i ∉ t then g (insert i t) else 0 := fun t => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ i : σ, (∑ t ∈ powersetCard k univ, if i ∉ t then g (insert i t) else 0) =
      ∑ u ∈ powersetCard (k + 1) univ, if i ∈ u then g u else 0 := by
    intro i
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun t => insert i t) (fun u => u.erase i) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at ht ⊢
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem ht.2, ht.1.2]⟩,
        Finset.mem_insert_self _ _⟩
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hu ⊢
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hu.2, hu.1.2]; rfl⟩,
        Finset.notMem_erase _ _⟩
    · intro t ht
      simp only [Finset.mem_filter] at ht
      exact Finset.erase_insert ht.2
    · intro u hu
      simp only [Finset.mem_filter] at hu
      exact Finset.insert_erase hu.2
    · intro t _; rfl
  simp_rw [h2]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← Finset.sum_filter, Finset.sum_const]
  congr 1
  rw [Finset.mem_powersetCard] at hu
  rw [← hu.2]; congr 1; ext; simp

/-- **`d(e_k) = e_1 e_k - (k+1) e_{k+1}`** (Ellis–Qi, Appendix A.4.2, corrected). -/
theorem pd_esymm (k : ℕ) :
    pd σ R (esymm σ R k) = esymm σ R 1 * esymm σ R k - (k + 1 : MvPolynomial σ R) *
      esymm σ R (k + 1) := by
  have hsum : esymm σ R 1 * esymm σ R k =
      pd σ R (esymm σ R k) + (k + 1 : MvPolynomial σ R) * esymm σ R (k + 1) := by
    rw [esymm_one]
    unfold esymm
    rw [map_sum, Finset.mul_sum]
    have : (k + 1 : MvPolynomial σ R) * ∑ u ∈ powersetCard (k + 1) univ, ∏ i ∈ u, X i =
        ∑ t ∈ powersetCard k univ, ∑ i ∈ univ \ t, ∏ j ∈ insert i t, (X j : MvPolynomial σ R) := by
      have h := sum_powersetCard_insert (M := MvPolynomial σ R) k (fun u => ∏ j ∈ u, X j)
      rw [h, nsmul_eq_mul]; push_cast; ring
    rw [this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pd_prod_X, ← Finset.sum_sdiff (Finset.subset_univ t), add_mul, add_comm]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.prod_insert (Finset.mem_sdiff.mp hi).2]
  rw [hsum]; ring

omit [DecidableEq σ] in
theorem eval_one_esymm (k : ℕ) :
    eval (fun _ => (1 : R)) (esymm σ R k) = ((Fintype.card σ).choose k : R) := by
  simp [esymm, map_sum, map_prod, Finset.card_powersetCard]

/-- The printed formula `d(e_k) = e_1 e_k - e_{k+1}` holds iff `k e_{k+1} = 0`. -/
theorem pd_esymm_printed_iff (k : ℕ) :
    pd σ R (esymm σ R k) = esymm σ R 1 * esymm σ R k - esymm σ R (k + 1) ↔
      (k : MvPolynomial σ R) * esymm σ R (k + 1) = 0 := by
  rw [pd_esymm]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- The printed formula `d(e_1) = e_1² - e_2` fails in two variables over `ℤ`. -/
theorem pd_esymm_printed_false :
    pd (Fin 2) ℤ (esymm (Fin 2) ℤ 1) ≠
      esymm (Fin 2) ℤ 1 * esymm (Fin 2) ℤ 1 - esymm (Fin 2) ℤ (1 + 1) := by
  rw [Ne, pd_esymm_printed_iff]
  intro h
  have := congrArg (eval (fun _ => (1 : ℤ))) h
  rw [map_mul, eval_one_esymm] at this
  simp at this

end Elementary

/-! ## Complete homogeneous symmetric polynomials -/

section Complete

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
theorem prod_map_X_toMultiset (P : σ →₀ ℕ) :
    ((Finsupp.toMultiset P).map (X : σ → MvPolynomial σ R)).prod = monomial P 1 := by
  induction P using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [map_add, Multiset.map_add, Multiset.prod_add, ih, Finsupp.toMultiset_single,
      Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton, Multiset.prod_singleton,
      X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- `h_k = Σ_{|β| = k} x^β`. -/
theorem hsymm_eq_sum (k : ℕ) :
    hsymm σ R k = ∑ β ∈ (univ : Finset σ).finsuppAntidiag k, monomial β 1 := by
  rw [hsymm]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun β hβ => ⟨Finsupp.toMultiset β, by
      rw [Finset.mem_finsuppAntidiag] at hβ
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simpa using hβ.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    have := Finsupp.card_toMultiset (Multiset.toFinsupp s.1)
    rw [Multiset.toFinsupp_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    simp only [id] at this
    rw [← this]; exact s.2
  · intro _ _; exact Finset.mem_univ _
  · intro s _; apply Subtype.ext; simp
  · intro β _; simp
  · intro s _
    have := prod_map_X_toMultiset (R := R) (Multiset.toFinsupp s.1)
    rw [Multiset.toFinsupp_toMultiset] at this
    exact this

omit [DecidableEq σ] in
theorem sum_univ_finsupp_add (f g : σ →₀ ℕ) :
    (univ : Finset σ).sum ⇑(f + g) = univ.sum ⇑f + univ.sum ⇑g := by
  rw [Finsupp.coe_add]; exact Finset.sum_add_distrib

theorem sum_antidiag_shift {M : Type*} [AddCommMonoid M] (k : ℕ) (i : σ) (F : (σ →₀ ℕ) → M) :
    ∑ β ∈ (univ : Finset σ).finsuppAntidiag k, F (β + Finsupp.single i 1) =
      ∑ γ ∈ ((univ : Finset σ).finsuppAntidiag (k + 1)).filter (fun γ => 1 ≤ γ i), F γ := by
  refine Finset.sum_nbij' (fun β => β + Finsupp.single i 1) (fun γ => γ - Finsupp.single i 1)
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hβ ⊢
    refine ⟨⟨?_, Finset.subset_univ _⟩, by simp⟩
    rw [sum_univ_finsupp_add, hβ.1]
    simp
  · intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hγ ⊢
    refine ⟨?_, Finset.subset_univ _⟩
    have hle : Finsupp.single i 1 ≤ γ := Finsupp.single_le_iff.mpr hγ.2
    have h := hγ.1.1
    rw [← tsub_add_cancel_of_le hle, sum_univ_finsupp_add,
      show (univ : Finset σ).sum ⇑(Finsupp.single i 1) = 1 by simp] at h
    omega
  · intro β _; simp
  · intro γ hγ
    simp only [Finset.mem_filter] at hγ
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hγ.2)
  · intro β _; rfl

/-- **`d(h_k) = (k+1) h_{k+1} - h_1 h_k`** (Ellis–Qi, Appendix A.4.2, corrected). -/
theorem pd_hsymm (k : ℕ) :
    pd σ R (hsymm σ R k) = (k + 1 : MvPolynomial σ R) * hsymm σ R (k + 1) -
      hsymm σ R 1 * hsymm σ R k := by
  have key : pd σ R (hsymm σ R k) + hsymm σ R 1 * hsymm σ R k =
      (k + 1 : MvPolynomial σ R) * hsymm σ R (k + 1) := by
    rw [hsymm_one, hsymm_eq_sum, hsymm_eq_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    have e1 : ∀ β : σ →₀ ℕ, pd σ R (monomial β 1) + (∑ i, X i) * monomial β 1 =
        ∑ i, monomial (β + Finsupp.single i 1) (((β + Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : R) := by
      intro β
      rw [pd_monomial', Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [X, monomial_mul_monomial, one_mul, add_comm (Finsupp.single i 1) β, ← map_add (monomial _)]
      congr 1
      simp
    simp_rw [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ i : σ, ∑ β ∈ (univ : Finset σ).finsuppAntidiag k,
        monomial (β + Finsupp.single i 1) (((β + Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : R) =
        ∑ γ ∈ (univ : Finset σ).finsuppAntidiag (k + 1), monomial γ ((γ i : ℕ) : R) := by
      intro i
      refine (sum_antidiag_shift k i (fun γ => monomial γ ((γ i : ℕ) : R))).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs with h
      · rfl
      · rw [show γ i = 0 by omega]; simp
    rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [← map_sum, ← Nat.cast_sum]
    rw [Finset.mem_finsuppAntidiag] at hγ
    rw [show ∑ i, γ i = k + 1 from hγ.1]
    rw [show (k + 1 : MvPolynomial σ R) = C ((k + 1 : ℕ) : R) by simp, C_mul_monomial, mul_one]
  rw [← key]; ring

theorem eval_one_hsymm_one_var (k : ℕ) :
    eval (fun _ => (1 : R)) (hsymm (Fin 1) R k) = 1 := by
  rw [hsymm_eq_sum, map_sum]
  simp only [eval_monomial, one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
  rw [Finset.sum_const, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp

/-- The printed formula `d(h_k) = h_{k+1} - h_1 h_k` holds iff `k h_{k+1} = 0`. -/
theorem pd_hsymm_printed_iff (k : ℕ) :
    pd σ R (hsymm σ R k) = hsymm σ R (k + 1) - hsymm σ R 1 * hsymm σ R k ↔
      (k : MvPolynomial σ R) * hsymm σ R (k + 1) = 0 := by
  rw [pd_hsymm]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- The printed formula `d(h_1) = h_2 - h_1²` fails in one variable over `ℤ`
(there `d(x) = x²` while `h_2 - h_1² = 0`). -/
theorem pd_hsymm_printed_false :
    pd (Fin 1) ℤ (hsymm (Fin 1) ℤ 1) ≠
      hsymm (Fin 1) ℤ (1 + 1) - hsymm (Fin 1) ℤ 1 * hsymm (Fin 1) ℤ 1 := by
  rw [Ne, pd_hsymm_printed_iff]
  intro h
  have := congrArg (eval (fun _ => (1 : ℤ))) h
  rw [map_mul, eval_one_hsymm_one_var] at this
  simp at this

end Complete

end

end OddMath.Frontier.EQPdg

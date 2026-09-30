import OddMath.Frontier.EQPdgPoly
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Module

/-!
# Alternants, Schur polynomials and the differential

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2 (the formula `d(s_λ) = Σ_{μ = λ + B} ct(B) s_μ`).

For `α : Fin n → ℕ` let `a_α = det(x_i^{α_j})` be the alternant (`alt`). We use the increasing
convention: `δ = (0, 1, …, n-1)` (`delta`), so `a_δ` is the Vandermonde determinant
`Π_{i<j} (x_j - x_i)`, and the `a_α` with `α` strictly increasing span the module `Alt` of
alternating polynomials (the image of the antisymmetrizer). Over an integral domain `R`:

* `symToAlt`: multiplication by `a_δ` is a linear isomorphism from symmetric polynomials onto
  `Alt` (the bialternant theorem);
* `schurA α = a_α / a_δ`, and for a partition `λ` with at most `n` parts, stored as an antitone
  function `λ : Fin n → ℕ` (`λ_0 ≥ λ_1 ≥ ⋯`), the Schur polynomial `schur λ = a_{λ+δ}/a_δ`
  (with `(λ+δ)_i = λ_{n-1-i} + i`);
* `pd_schur`: **`d(s_λ) = Σ_B ct(B) s_{λ+B}`**, the sum over the addable boxes `B` of `λ` lying
  in the first `n` rows (i.e. over rows `r` such that `λ + e_r` is again a partition), where
  the box added in row `r` (`0`-indexed) has content `λ_r - r` (column minus row). A partition
  with more than `n` rows has `s_μ = 0` in `n` variables, so this is the paper's formula in
  `n` variables.

The key identity is `D(a_α) = Σ_i (α_i - (n-1)) a_{α + e_i}` for the operator
`D = d - (n-1) e_1` (`dAlt_alt`), together with `D(a_δ · f) = a_δ · d(f)`
(`dAlt_vandermonde_mul`).
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset Matrix Equiv

noncomputable section

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ## Monomials and alternants -/

/-- The monomial `x^β = Π_i x_i^{β_i}`. -/
def xpow (β : Fin n → ℕ) : MvPolynomial (Fin n) R := ∏ i, X i ^ β i

theorem xpow_eq_monomial (β : Fin n → ℕ) :
    (xpow β : MvPolynomial (Fin n) R) = monomial (Finsupp.equivFunOnFinite.symm β) 1 := by
  rw [xpow, monomial_eq, C_1, one_mul, Finsupp.prod_fintype]
  · rfl
  · intro i; simp

theorem monomial_eq_smul_xpow (β : Fin n →₀ ℕ) (c : R) :
    monomial β c = c • xpow (⇑β) := by
  rw [xpow_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    show Finsupp.equivFunOnFinite.symm ⇑β = β from Finsupp.equivFunOnFinite.symm_apply_apply β]

theorem rename_xpow (σ : Perm (Fin n)) (β : Fin n → ℕ) :
    rename σ (xpow β : MvPolynomial (Fin n) R) = xpow (fun i => β (σ.symm i)) := by
  rw [xpow, map_prod, xpow]
  simp only [map_pow, rename_X]
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

theorem xpow_add (β γ : Fin n → ℕ) :
    (xpow (β + γ) : MvPolynomial (Fin n) R) = xpow β * xpow γ := by
  simp [xpow, pow_add, Finset.prod_mul_distrib]

theorem X_mul_xpow (i : Fin n) (β : Fin n → ℕ) :
    (X i * xpow β : MvPolynomial (Fin n) R) = xpow (β + Pi.single i 1) := by
  rw [xpow_add, mul_comm]
  congr 1
  rw [xpow, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- The alternant `a_α = det(x_i^{α_j})`. -/
def alt (α : Fin n → ℕ) : MvPolynomial (Fin n) R :=
  (Matrix.of fun i j => (X i ^ α j : MvPolynomial (Fin n) R)).det

/-- The antisymmetrizer `f ↦ Σ_σ sgn(σ) σ(f)`. -/
def antisymm : MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R :=
  ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : R) • (rename σ).toLinearMap

theorem antisymm_apply (f : MvPolynomial (Fin n) R) :
    antisymm f = ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : R) • rename σ f := by
  simp [antisymm, LinearMap.sum_apply]

theorem alt_eq_antisymm (α : Fin n → ℕ) :
    (alt α : MvPolynomial (Fin n) R) = antisymm (xpow α) := by
  rw [alt, det_apply', antisymm_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [xpow, map_prod, smul_eq_C_mul, map_intCast]
  simp

/-- An endomorphism commuting with all variable permutations commutes with the
antisymmetrizer. -/
theorem antisymm_comm (O : Module.End R (MvPolynomial (Fin n) R))
    (hO : ∀ (σ : Perm (Fin n)) f, O (rename σ f) = rename σ (O f)) (f : MvPolynomial (Fin n) R) :
    O (antisymm f) = antisymm (O f) := by
  simp only [antisymm_apply, map_sum, map_smul, hO]

theorem antisymm_mul_symmetric {g : MvPolynomial (Fin n) R} (hg : g.IsSymmetric)
    (f : MvPolynomial (Fin n) R) : antisymm (g * f) = g * antisymm f := by
  simp only [antisymm_apply, map_mul, hg _, Finset.mul_sum, mul_smul_comm]

theorem antisymm_eq_sum_alt (f : MvPolynomial (Fin n) R) :
    antisymm f = ∑ β ∈ f.support, f.coeff β • alt (⇑β) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [monomial_eq_smul_xpow, map_smul, alt_eq_antisymm]

/-- The module of alternating polynomials: the image of the antisymmetrizer. -/
def Alt : Submodule R (MvPolynomial (Fin n) R) := LinearMap.range antisymm

theorem alt_mem (α : Fin n → ℕ) : (alt α : MvPolynomial (Fin n) R) ∈ Alt := by
  rw [alt_eq_antisymm]; exact ⟨_, rfl⟩

theorem Alt_eq_span : (Alt : Submodule R (MvPolynomial (Fin n) R)) =
    Submodule.span R (Set.range fun α : Fin n → ℕ => alt α) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [antisymm_eq_sum_alt]
    exact Submodule.sum_mem _ fun β _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact alt_mem α

theorem antisymm_mem_Alt_of_comm (O : Module.End R (MvPolynomial (Fin n) R))
    (hO : ∀ (σ : Perm (Fin n)) f, O (rename σ f) = rename σ (O f))
    {f : MvPolynomial (Fin n) R} (hf : f ∈ Alt) : O f ∈ Alt := by
  obtain ⟨g, rfl⟩ := hf
  rw [antisymm_comm O hO]
  exact ⟨_, rfl⟩

/-! ## Basic properties of alternants -/

theorem alt_comp_perm (α : Fin n → ℕ) (τ : Perm (Fin n)) :
    (alt (α ∘ τ) : MvPolynomial (Fin n) R) = ((Perm.sign τ : ℤ) : MvPolynomial (Fin n) R) *
      alt α := by
  unfold alt
  rw [← det_permute']
  rfl

theorem alt_eq_zero_of_not_injective {α : Fin n → ℕ} (hα : ¬ Function.Injective α) :
    (alt α : MvPolynomial (Fin n) R) = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, j, hij, hne⟩ := hα
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

theorem rename_alt (τ : Perm (Fin n)) (α : Fin n → ℕ) :
    rename τ (alt α : MvPolynomial (Fin n) R) =
      ((Perm.sign τ : ℤ) : MvPolynomial (Fin n) R) * alt α := by
  unfold alt
  rw [AlgHom.map_det, ← det_permute]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply]

/-- The substitution `x_a ↦ x_b`. -/
def substX (a b : Fin n) : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (Function.update X a (X b))

theorem substX_alt {a b : Fin n} (hab : a ≠ b) (α : Fin n → ℕ) :
    substX a b (alt α : MvPolynomial (Fin n) R) = 0 := by
  rw [alt, AlgHom.map_det]
  refine det_zero_of_row_eq hab ?_
  ext j
  simp [AlgHom.mapMatrix_apply, substX, Function.update_of_ne hab.symm]

/-- The Vandermonde exponent `δ = (0, 1, …, n-1)`. -/
def delta (n : ℕ) : Fin n → ℕ := fun i => i

theorem alt_delta :
    (alt (delta n) : MvPolynomial (Fin n) R) = ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i) := by
  rw [alt, ← det_vandermonde]
  rfl

/-! ## Coefficients: linear independence of the `a_α`, `α` strictly increasing -/

theorem perm_eq_one_of_strictMono {α : Fin n → ℕ} (hα : StrictMono α) {π : Perm (Fin n)}
    (hπ : Monotone (α ∘ π)) : π = 1 := by
  have h1 : π = Tuple.sort α := by
    rw [Tuple.eq_sort_iff]
    refine ⟨hπ, fun i j hij heq => ?_⟩
    exact absurd (π.injective (hα.injective heq)) (ne_of_lt hij)
  have h2 : (1 : Perm (Fin n)) = Tuple.sort α := by
    rw [Tuple.eq_sort_iff]
    refine ⟨by simpa using hα.monotone, fun i j hij heq => ?_⟩
    exact absurd (hα.injective heq) (ne_of_lt hij)
  rw [h1, ← h2]

theorem coeff_rename_xpow (π : Perm (Fin n)) (α β : Fin n → ℕ) :
    (rename π (xpow α) : MvPolynomial (Fin n) R).coeff (Finsupp.equivFunOnFinite.symm β) =
      if (fun i => α (π.symm i)) = β then 1 else 0 := by
  rw [rename_xpow, xpow_eq_monomial, coeff_monomial]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem coeff_alt_strictMono {α β : Fin n → ℕ} (hα : StrictMono α) (hβ : StrictMono β) :
    (alt α : MvPolynomial (Fin n) R).coeff (Finsupp.equivFunOnFinite.symm β) =
      if α = β then 1 else 0 := by
  rw [alt_eq_antisymm, antisymm_apply, coeff_sum]
  simp only [coeff_smul, coeff_rename_xpow, smul_eq_mul]
  have h1 : (1 : Perm (Fin n)).symm = 1 := rfl
  rw [Finset.sum_eq_single 1]
  · simp [h1]
  · intro π _ hπ
    split_ifs with h'
    · exfalso
      apply hπ
      have hmono : Monotone (α ∘ π.symm) := by
        rw [show α ∘ π.symm = β from h']; exact hβ.monotone
      have := congrArg Equiv.symm (perm_eq_one_of_strictMono hα (π := π.symm) hmono)
      simpa [h1] using this
    · simp
  · simp

/-- Sorting: every `a_γ` is `0` or `± a_α` with `α` strictly increasing. -/
theorem alt_mem_span_strictMono (γ : Fin n → ℕ) :
    (alt γ : MvPolynomial (Fin n) R) ∈
      Submodule.span R (Set.range fun α : {α : Fin n → ℕ // StrictMono α} => alt α.1) := by
  by_cases hγ : Function.Injective γ
  · set τ := Tuple.sort γ
    have hmono : StrictMono (γ ∘ τ) :=
      (Tuple.monotone_sort γ).strictMono_of_injective (hγ.comp τ.injective)
    have h := alt_comp_perm (R := R) γ τ
    have hs : (alt γ : MvPolynomial (Fin n) R) =
        ((Perm.sign τ : ℤ) : R) • alt (γ ∘ τ) := by
      rw [h, smul_eq_C_mul, map_intCast, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
        Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hmono⟩, rfl⟩)
  · rw [alt_eq_zero_of_not_injective hγ]
    exact Submodule.zero_mem _

theorem coeff_alt_subtype (β γ : {α : Fin n → ℕ // StrictMono α}) :
    (alt β.1 : MvPolynomial (Fin n) R).coeff (Finsupp.equivFunOnFinite.symm γ.1) =
      if β = γ then 1 else 0 := by
  rw [coeff_alt_strictMono β.2 γ.2]
  simp only [Subtype.ext_iff]

theorem linearIndependent_alt :
    LinearIndependent R (fun α : {α : Fin n → ℕ // StrictMono α} =>
      (alt α.1 : MvPolynomial (Fin n) R)) := by
  rw [linearIndependent_iff']
  intro s c hs α hα
  have := congrArg (fun q : MvPolynomial (Fin n) R => q.coeff (Finsupp.equivFunOnFinite.symm α.1)) hs
  simp only [coeff_sum, coeff_smul, coeff_alt_subtype, smul_eq_mul] at this
  rw [Finset.sum_eq_single α] at this
  · simpa using this
  · intro β _ hβ
    simp [hβ]
  · intro h; exact absurd hα h

/-- The basis `{a_α : α strictly increasing}` of `Alt`. -/
def altBasis : Module.Basis {α : Fin n → ℕ // StrictMono α} R
    (Alt : Submodule R (MvPolynomial (Fin n) R)) :=
  Module.Basis.span (linearIndependent_alt) |>.map (LinearEquiv.ofEq _ _ (by
    rw [Alt_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨α, rfl⟩
      exact Submodule.subset_span ⟨α.1, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      exact alt_mem_span_strictMono γ))

theorem altBasis_apply (α : {α : Fin n → ℕ // StrictMono α}) :
    (altBasis (n := n) (R := R) α).1 = alt α.1 := by
  simp [altBasis, Module.Basis.span_apply]

/-! ## The operator `D = d - (n-1) e_1` -/

/-- `D = d - (n-1) e_1`, which corresponds to `d` under multiplication by `a_δ`. -/
def dAlt : Module.End R (MvPolynomial (Fin n) R) :=
  pdL (Fin n) R - ((n : R) - 1) • LinearMap.mulLeft R (esymm (Fin n) R 1)

theorem dAlt_apply (f : MvPolynomial (Fin n) R) :
    dAlt f = pd (Fin n) R f - ((n : R) - 1) • (esymm (Fin n) R 1 * f) := rfl

theorem dAlt_rename (σ : Perm (Fin n)) (f : MvPolynomial (Fin n) R) :
    dAlt (rename σ f) = rename σ (dAlt f) := by
  rw [dAlt_apply, dAlt_apply, map_sub, map_smul, map_mul, pd_rename,
    (esymm_isSymmetric (Fin n) R 1) σ]

theorem pd_xpow (β : Fin n → ℕ) :
    pd (Fin n) R (xpow β) = ∑ i, ((β i : ℕ) : R) • xpow (β + Pi.single i 1) := by
  classical
  rw [xpow_eq_monomial, pd_monomial']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [monomial_eq_smul_xpow, one_mul]
  congr 2
  ext j
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

theorem dAlt_xpow (β : Fin n → ℕ) :
    dAlt (xpow β : MvPolynomial (Fin n) R) =
      ∑ i, (((β i : ℕ) : R) - ((n : R) - 1)) • xpow (β + Pi.single i 1) := by
  rw [dAlt_apply, pd_xpow, esymm_one, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [X_mul_xpow]
  module

/-- `D(a_α) = Σ_i (α_i - (n-1)) a_{α + e_i}`. -/
theorem dAlt_alt (α : Fin n → ℕ) :
    dAlt (alt α : MvPolynomial (Fin n) R) =
      ∑ i, (((α i : ℕ) : R) - ((n : R) - 1)) • alt (α + Pi.single i 1) := by
  rw [alt_eq_antisymm, antisymm_comm _ dAlt_rename, dAlt_xpow, map_sum]
  simp only [map_smul, alt_eq_antisymm]

theorem dAlt_alt_delta : dAlt (alt (delta n) : MvPolynomial (Fin n) R) = 0 := by
  rw [dAlt_alt]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : (i : ℕ) + 1 < n
  · rw [alt_eq_zero_of_not_injective, smul_zero]
    intro hinj
    have := @hinj i ⟨i + 1, hi⟩ (by simp [delta, Fin.ext_iff])
    simp [Fin.ext_iff] at this
  · have : (i : ℕ) = n - 1 := by omega
    rw [show ((delta n i : ℕ) : R) - ((n : R) - 1) = 0 by
      simp only [delta, this]
      have hn : 1 ≤ n := by have := i.2; omega
      rw [Nat.cast_sub hn]; ring, zero_smul]

theorem dAlt_mul (g f : MvPolynomial (Fin n) R) :
    dAlt (g * f) = dAlt g * f + g * pd (Fin n) R f := by
  rw [dAlt_apply, dAlt_apply, Derivation.leibniz]
  simp only [smul_eq_mul, smul_eq_C_mul]
  ring

theorem dAlt_vandermonde_mul (f : MvPolynomial (Fin n) R) :
    dAlt (alt (delta n) * f) = alt (delta n) * pd (Fin n) R f := by
  rw [dAlt_mul, dAlt_alt_delta, zero_mul, zero_add]

/-! ## The bialternant theorem over a domain -/

section Domain

variable [IsDomain R]

omit [IsDomain R] in
theorem substX_apply_X (a b c : Fin n) :
    substX a b (X c : MvPolynomial (Fin n) R) = X (if c = a then b else c) := by
  simp only [substX, aeval_X, Function.update_apply]
  split_ifs <;> rfl

omit [IsDomain R] in
theorem dvd_of_substX {a b : Fin n} (f : MvPolynomial (Fin n) R)
    (hf : substX a b f = 0) : (X b - X a : MvPolynomial (Fin n) R) ∣ f := by
  rw [← Ideal.mem_span_singleton]
  set I := Ideal.span {(X b - X a : MvPolynomial (Fin n) R)}
  have hcomp : (Ideal.Quotient.mkₐ R I).comp (substX a b) = Ideal.Quotient.mkₐ R I := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, substX_apply_X, Ideal.Quotient.mkₐ_eq_mk]
    split_ifs with h
    · subst h
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton_self _
    · rfl
  have := congrArg (fun φ => φ f) hcomp
  simp only [AlgHom.comp_apply, hf, map_zero] at this
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← this]

theorem substX_X_sub_ne_zero {a b c e : Fin n} (hab : a < b) (hce : c < e)
    (hne : (a, b) ≠ (c, e)) :
    substX a b (X e - X c : MvPolynomial (Fin n) R) ≠ 0 := by
  rw [map_sub, substX_apply_X, substX_apply_X, sub_ne_zero]
  intro h
  have h := X_injective h
  rw [Fin.lt_def] at hab hce
  simp only [Prod.mk.injEq, ne_eq, Fin.ext_iff] at hne
  split_ifs at h with h1 h2 h2 <;> simp only [Fin.ext_iff] at h h1 h2 <;> omega

/-- If `f` vanishes under every substitution `x_i ↦ x_j` with `(i, j) ∈ S`, `i < j`, then
`Π_{(i,j) ∈ S} (x_j - x_i)` divides `f`. -/
theorem prod_dvd_of_substX (S : Finset (Fin n × Fin n)) (hS : ∀ q ∈ S, q.1 < q.2)
    (f : MvPolynomial (Fin n) R) (hf : ∀ q ∈ S, substX q.1 q.2 f = 0) :
    (∏ q ∈ S, (X q.2 - X q.1) : MvPolynomial (Fin n) R) ∣ f := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | insert q S hq ih =>
    obtain ⟨g, rfl⟩ := dvd_of_substX f (hf q (Finset.mem_insert_self _ _))
    rw [Finset.prod_insert hq]
    refine mul_dvd_mul_left _ (ih (fun q' hq' => hS q' (Finset.mem_insert_of_mem hq')) g ?_)
    intro q' hq'
    have h0 := hf q' (Finset.mem_insert_of_mem hq')
    rw [map_mul] at h0
    refine (mul_eq_zero.mp h0).resolve_left ?_
    refine substX_X_sub_ne_zero (hS q' (Finset.mem_insert_of_mem hq'))
      (hS q (Finset.mem_insert_self _ _)) ?_
    intro h; apply hq; rw [show q = q' from by rw [Prod.ext_iff] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩]
    exact hq'

omit [IsDomain R] in
theorem alt_delta_eq_prod_pairs :
    (alt (delta n) : MvPolynomial (Fin n) R) =
      ∏ q ∈ (univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2), (X q.2 - X q.1) := by
  rw [alt_delta, Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j; simp

theorem alt_delta_ne_zero : (alt (delta n) : MvPolynomial (Fin n) R) ≠ 0 := by
  rw [alt_delta, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [sub_ne_zero]
  intro h
  have := X_injective h
  rw [Finset.mem_Ioi] at hj
  exact absurd this (ne_of_gt hj)

omit [IsDomain R] in
theorem Alt_substX {a b : Fin n} (hab : a ≠ b) {f : MvPolynomial (Fin n) R} (hf : f ∈ Alt) :
    substX a b f = 0 := by
  rw [Alt_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨α, rfl⟩ := hx; exact substX_alt hab α
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

omit [IsDomain R] in
theorem Alt_rename (τ : Perm (Fin n)) {f : MvPolynomial (Fin n) R} (hf : f ∈ Alt) :
    rename τ f = ((Perm.sign τ : ℤ) : MvPolynomial (Fin n) R) * f := by
  rw [Alt_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨α, rfl⟩ := hx; exact rename_alt τ α
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, mul_add]
  | smul c x _ hx => rw [map_smul, hx, mul_smul_comm]

/-- Every alternating polynomial is `a_δ` times a symmetric polynomial. -/
theorem exists_symmetric_of_mem_Alt {f : MvPolynomial (Fin n) R} (hf : f ∈ Alt) :
    ∃ g : MvPolynomial (Fin n) R, g.IsSymmetric ∧ f = alt (delta n) * g := by
  have hdvd : (alt (delta n) : MvPolynomial (Fin n) R) ∣ f := by
    rw [alt_delta_eq_prod_pairs]
    refine prod_dvd_of_substX _ (fun q hq => (Finset.mem_filter.mp hq).2) f fun q hq => ?_
    exact Alt_substX (ne_of_lt (Finset.mem_filter.mp hq).2) hf
  obtain ⟨g, rfl⟩ := hdvd
  refine ⟨g, fun τ => ?_, rfl⟩
  have h1 := Alt_rename τ hf
  rw [map_mul, rename_alt] at h1
  have hs : ((Perm.sign τ : ℤ) : MvPolynomial (Fin n) R) * alt (delta n) ≠ 0 := by
    refine mul_ne_zero ?_ alt_delta_ne_zero
    rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> simp [h]
  rw [← mul_assoc] at h1
  exact mul_left_cancel₀ hs h1

/-- Symmetric polynomials as a submodule. -/
abbrev SymSub : Submodule R (MvPolynomial (Fin n) R) :=
  Subalgebra.toSubmodule (symmetricSubalgebra (Fin n) R)

omit [IsDomain R] in
theorem mem_SymSub {f : MvPolynomial (Fin n) R} : f ∈ (SymSub : Submodule R _) ↔ f.IsSymmetric :=
  mem_symmetricSubalgebra f

omit [IsDomain R] in
theorem vandermonde_mul_mem_Alt {f : MvPolynomial (Fin n) R} (hf : f.IsSymmetric) :
    alt (delta n) * f ∈ (Alt : Submodule R (MvPolynomial (Fin n) R)) := by
  rw [alt_eq_antisymm, mul_comm, ← antisymm_mul_symmetric hf]
  exact ⟨_, rfl⟩

/-- **Bialternant theorem**: multiplication by `a_δ` is an isomorphism from symmetric
polynomials onto alternating polynomials. -/
def symToAlt : (SymSub : Submodule R (MvPolynomial (Fin n) R)) ≃ₗ[R]
    (Alt : Submodule R (MvPolynomial (Fin n) R)) :=
  LinearEquiv.ofBijective
    ((LinearMap.mulLeft R (alt (delta n))).restrict fun f hf =>
      vandermonde_mul_mem_Alt (mem_SymSub.mp hf))
    ⟨fun f g h => by
      have := congrArg Subtype.val h
      simp only [LinearMap.restrict_apply, LinearMap.mulLeft_apply] at this
      exact Subtype.ext (mul_left_cancel₀ alt_delta_ne_zero this),
     fun ⟨f, hf⟩ => by
      obtain ⟨g, hg, rfl⟩ := exists_symmetric_of_mem_Alt hf
      exact ⟨⟨g, mem_SymSub.mpr hg⟩, rfl⟩⟩

theorem symToAlt_apply (f : (SymSub : Submodule R (MvPolynomial (Fin n) R))) :
    (symToAlt f).1 = alt (delta n) * f.1 := rfl

/-- `s_α = a_α / a_δ` (for any exponent `α`; it is `0` unless `α` is injective). -/
def schurA (α : Fin n → ℕ) : MvPolynomial (Fin n) R :=
  (symToAlt.symm ⟨alt α, alt_mem α⟩ : (SymSub : Submodule R (MvPolynomial (Fin n) R)))

theorem vandermonde_mul_schurA (α : Fin n → ℕ) :
    alt (delta n) * (schurA α : MvPolynomial (Fin n) R) = alt α := by
  have h := (symToAlt (R := R) (n := n)).apply_symm_apply ⟨alt α, alt_mem α⟩
  have := congrArg Subtype.val h
  rw [symToAlt_apply] at this
  exact this

theorem schurA_isSymmetric (α : Fin n → ℕ) : (schurA α : MvPolynomial (Fin n) R).IsSymmetric :=
  mem_SymSub.mp (symToAlt.symm ⟨alt α, alt_mem α⟩).2

theorem eq_schurA_of_mul {α : Fin n → ℕ} {g : MvPolynomial (Fin n) R}
    (h : alt (delta n) * g = alt α) : g = schurA α :=
  mul_left_cancel₀ alt_delta_ne_zero (h.trans (vandermonde_mul_schurA α).symm)

theorem schurA_eq_zero_of_not_injective {α : Fin n → ℕ} (hα : ¬ Function.Injective α) :
    (schurA α : MvPolynomial (Fin n) R) = 0 :=
  (eq_schurA_of_mul (by rw [mul_zero, alt_eq_zero_of_not_injective hα])).symm

/-- **`d(s_α) = Σ_i (α_i - (n-1)) s_{α + e_i}`**. -/
theorem pd_schurA (α : Fin n → ℕ) :
    pd (Fin n) R (schurA α) =
      ∑ i, (((α i : ℕ) : R) - ((n : R) - 1)) • schurA (α + Pi.single i 1) := by
  refine mul_left_cancel₀ (alt_delta_ne_zero (R := R)) ?_
  rw [← dAlt_vandermonde_mul, vandermonde_mul_schurA, dAlt_alt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, vandermonde_mul_schurA]

/-- The Schur polynomials `s_α`, `α` strictly increasing, form a basis of `Sym_n`. -/
def schurBasis : Module.Basis {α : Fin n → ℕ // StrictMono α} R
    (SymSub : Submodule R (MvPolynomial (Fin n) R)) :=
  altBasis.map symToAlt.symm

theorem schurBasis_apply (α : {α : Fin n → ℕ // StrictMono α}) :
    (schurBasis (n := n) (R := R) α).1 = schurA α.1 := by
  rw [schurBasis, Module.Basis.map_apply]
  congr 2
  exact Subtype.ext (altBasis_apply α)

/-! ## Partitions -/

/-- The exponent `λ + δ` of a partition `λ` (antitone, `λ_0 ≥ λ_1 ≥ ⋯`) in the increasing
convention: `(λ + δ)_i = λ_{n-1-i} + i`. -/
def lamDelta (lam : Fin n → ℕ) : Fin n → ℕ := fun i => lam i.rev + i

/-- The Schur polynomial `s_λ = a_{λ+δ}/a_δ` of a partition `λ` with at most `n` parts. -/
def schur (lam : Fin n → ℕ) : MvPolynomial (Fin n) R := schurA (lamDelta lam)

theorem lamDelta_add_single (lam : Fin n → ℕ) (r : Fin n) :
    lamDelta (lam + Pi.single r 1) = lamDelta lam + Pi.single r.rev 1 := by
  funext i
  simp only [lamDelta, Pi.add_apply, Pi.single_apply, Fin.rev_eq_iff]
  split_ifs <;> omega

theorem strictMono_lamDelta {μ : Fin n → ℕ} (h : Antitone μ) : StrictMono (lamDelta μ) := by
  intro i j hij
  simp only [lamDelta]
  have h1 : μ j.rev ≥ μ i.rev := h (Fin.rev_le_rev.mpr hij.le)
  have h2 : (i : ℕ) < j := hij
  omega

theorem injective_lamDelta_iff {lam : Fin n → ℕ} (hlam : Antitone lam) (r : Fin n) :
    Function.Injective (lamDelta (lam + Pi.single r 1)) ↔ Antitone (lam + Pi.single r 1) := by
  constructor
  · intro hinj a b hab
    by_contra hlt
    rw [not_le] at hlt
    have hμ : ∀ c, (lam + Pi.single r 1 : Fin n → ℕ) c = lam c + if c = r then 1 else 0 :=
      fun c => by simp [Pi.single_apply]
    rw [hμ, hμ] at hlt
    have hlab := hlam hab
    have hbr : b = r := by
      by_contra h
      simp only [h, ↓reduceIte, add_zero] at hlt
      split_ifs at hlt <;> omega
    subst hbr
    have hne : a ≠ b := by rintro rfl; simp at hlt
    simp only [hne, ↓reduceIte, add_zero] at hlt
    have hab' : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h))
    obtain ⟨c, hc⟩ : ∃ c : Fin n, (c : ℕ) = b - 1 := ⟨⟨b - 1, by omega⟩, rfl⟩
    have hac : a ≤ c := by rw [Fin.le_def]; omega
    have hcb : c ≤ b := by rw [Fin.le_def]; omega
    have h1 := hlam hac
    have h2 := hlam hcb
    have hcne : c ≠ b := by intro h; rw [Fin.ext_iff] at h; omega
    have hbn := b.2
    have key : lamDelta (lam + Pi.single b 1) c.rev = lamDelta (lam + Pi.single b 1) b.rev := by
      simp only [lamDelta, Fin.rev_rev, hμ, hcne, ↓reduceIte, add_zero, Fin.val_rev]
      omega
    exact hcne (Fin.rev_injective (hinj key))
  · intro h; exact (strictMono_lamDelta h).injective

/-- **Ellis–Qi, Appendix A.4.2: `d(s_λ) = Σ_{μ = λ + B} ct(B) s_μ`** in `n` variables. The sum
runs over the rows `r` (`0`-indexed) such that `λ + e_r` is a partition, i.e. over the addable
boxes `B = (r, λ_r)` in the first `n` rows, and `ct(B) = λ_r - r`. -/
theorem pd_schur {lam : Fin n → ℕ} (hlam : Antitone lam) :
    pd (Fin n) R (schur lam) = ∑ r : Fin n,
      if Antitone (lam + Pi.single r 1) then
        (((lam r : ℕ) : R) - ((r : ℕ) : R)) • schur (lam + Pi.single r 1) else 0 := by
  rw [schur, pd_schurA]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← lamDelta_add_single]
  split_ifs with h
  · rw [schur]
    congr 1
    simp only [lamDelta, Fin.rev_rev, Fin.val_rev]
    have := r.2
    rw [Nat.cast_add, Nat.cast_sub (show (r : ℕ) + 1 ≤ n by omega)]
    push_cast
    ring
  · rw [schurA_eq_zero_of_not_injective, smul_zero]
    rw [injective_lamDelta_iff hlam]
    exact h

end Domain

end

end OddMath.Frontier.EQPdg

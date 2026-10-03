import OddMath.Frontier.EQPdgAlt
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Symmetric polynomials under `x_{n+1} ↦ 0`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2: "The map `d` is compatible with the inverse system `Sym_{n+1} → Sym_n`,
`x_i ↦ x_i` (`1 ≤ i ≤ n`), `x_{n+1} ↦ 0`."

This file collects the polynomial-level facts about that inverse system (over any commutative
ring `R`, variables `x_0, …, x_{n-1}`):

* `proj R n : R[x_0, …, x_n] → R[x_0, …, x_{n-1}]`, `x_0 ↦ 0`, `x_{i+1} ↦ x_i`. On symmetric
  polynomials it agrees with the printed map `projLast` (`x_n ↦ 0`, the other variables fixed):
  `projLast_eq_proj`. It commutes with `d` (`proj_pd`), preserves symmetric polynomials
  (`proj_isSymmetric`), and `coeff_proj` computes its coefficients;
* `eq_zero_of_proj_eq_zero`: a symmetric polynomial in `n + 1` variables of total degree `≤ n`
  which vanishes at `x_{n+1} = 0` is zero (the inverse system is eventually constant in each
  degree);
* `trunc σ R D`: the part of total degree `≤ D`; it commutes with every linear map which shifts
  the degree of monomials by a constant (`trunc_map`), in particular with renaming of variables,
  with `proj`, and `trunc (D + m) ∘ d^m = d^m ∘ trunc D` (`trunc_pd_pow`);
* stability: `proj_esymm`, `proj_hsymm`, and for the Schur polynomials `s_λ = a_{λ+δ}/a_δ`
  (over a domain): `proj_schur_of_last_eq_zero` (`s_λ(x_1, …, x_n, 0) = s_λ(x_1, …, x_n)` if
  `λ_{n+1} = 0`) and `proj_schur_of_last_ne_zero` (`s_λ(x_1, …, x_n, 0) = 0` if `λ_{n+1} ≠ 0`);
* homogeneity: `esymm_isHomogeneous`, `hsymm_isHomogeneous`, `alt_isHomogeneous`,
  `schur_isHomogeneous` (`s_λ` is homogeneous of degree `|λ|`).
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset

noncomputable section

/-! ## The projection `x_0 ↦ 0`, `x_{i+1} ↦ x_i` -/

section Proj

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The images of the variables: `x_0 ↦ 0`, `x_{i+1} ↦ x_i`. -/
def projVar : Fin (n + 1) → MvPolynomial (Fin n) R :=
  fun i => Fin.cases (motive := fun _ => MvPolynomial (Fin n) R) 0 X i

/-- The projection `R[x_0, …, x_n] → R[x_0, …, x_{n-1}]`, `x_0 ↦ 0`, `x_{i+1} ↦ x_i`. -/
def proj : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (projVar R n)

/-- The printed projection: `x_n ↦ 0` (the last variable), `x_i ↦ x_i` for `i < n`. -/
def projLast : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun i => Fin.lastCases (motive := fun _ => MvPolynomial (Fin n) R) 0 X i

variable {R n}

@[simp] theorem projVar_zero : projVar R n 0 = 0 := by simp [projVar]

@[simp] theorem projVar_succ (i : Fin n) : projVar R n i.succ = X i := by simp [projVar]

@[simp] theorem proj_X_zero : proj R n (X 0) = 0 := by rw [proj, aeval_X, projVar_zero]

@[simp] theorem proj_X_succ (i : Fin n) : proj R n (X i.succ) = X i := by
  rw [proj, aeval_X, projVar_succ]

@[simp] theorem proj_C (r : R) : proj R n (C r) = C r := algHom_C _ r

theorem proj_comp_rename_finRotate :
    (proj R n).comp (rename (finRotate (n + 1))) = projLast R n := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, rename_X, projLast, aeval_X]
  induction i using Fin.lastCases with
  | last => rw [finRotate_last, proj_X_zero, Fin.lastCases_last]
  | cast i =>
    have h : finRotate (n + 1) i.castSucc = i.succ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
      simp
    rw [h, proj_X_succ, Fin.lastCases_castSucc]

/-- On symmetric polynomials the printed projection `x_n ↦ 0` is `proj`. -/
theorem projLast_eq_proj {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsSymmetric) :
    projLast R n f = proj R n f := by
  rw [← proj_comp_rename_finRotate, AlgHom.comp_apply, hf]

/-- The projection commutes with the differential `d(x_i) = x_i²`. -/
theorem proj_pd (f : MvPolynomial (Fin (n + 1)) R) :
    proj R n (pd (Fin (n + 1)) R f) = pd (Fin n) R (proj R n f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, map_mul, pd_X, map_pow, hf]
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp

theorem proj_rename (e : Equiv.Perm (Fin n)) (f : MvPolynomial (Fin (n + 1)) R) :
    rename e (proj R n f) =
      proj R n (rename (Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), e)) f) := by
  have h : (rename e).comp (proj R n) =
      (proj R n).comp (rename (Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), e))) := by
    apply MvPolynomial.algHom_ext
    intro i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  exact AlgHom.congr_fun h f

/-- The projection of a symmetric polynomial is symmetric. -/
theorem proj_isSymmetric {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsSymmetric) :
    (proj R n f).IsSymmetric := fun e => by rw [proj_rename, hf]

theorem proj_eq_coeff_zero (f : MvPolynomial (Fin (n + 1)) R) :
    proj R n f = Polynomial.coeff (finSuccEquiv R n f) 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : (proj R n : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R) =
      (Polynomial.evalRingHom 0).comp
        (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [finSuccEquiv_apply]
    · intro i
      induction i using Fin.cases with
      | zero => simp [finSuccEquiv_X_zero]
      | succ i => simp [finSuccEquiv_X_succ]
  exact RingHom.congr_fun h f

/-- The coefficients of the projection: `[x^b] f(0, x) = [x_0^0 x^b] f`. -/
theorem coeff_proj (b : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) :
    (proj R n f).coeff b = f.coeff (b.cons 0) := by
  rw [proj_eq_coeff_zero, finSuccEquiv_coeff_coeff]

/-- **The inverse system is eventually constant in each degree**: a symmetric polynomial in
`n + 1` variables of total degree `≤ n` which vanishes at `x_{n+1} = 0` is zero. -/
theorem eq_zero_of_proj_eq_zero {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsSymmetric)
    (hdeg : f.totalDegree ≤ n) (h0 : proj R n f = 0) : f = 0 := by
  ext a
  rw [AddMonoidAlgebra.coeff_zero]
  by_contra hne
  have hle := le_totalDegree (mem_support_iff.mpr hne)
  -- some variable does not occur in `x^a`
  have hex : ∃ j, a j = 0 := by
    by_contra hall
    have h1 : ∀ j, 1 ≤ a j := fun j => Nat.one_le_iff_ne_zero.mpr fun h => hall ⟨j, h⟩
    have h2 : n + 1 ≤ ∑ j, a j := by
      calc n + 1 = ∑ _j : Fin (n + 1), 1 := by simp
        _ ≤ ∑ j, a j := Finset.sum_le_sum fun j _ => h1 j
    have h3 : (a.sum fun _ e => e) = ∑ j, a j := Finsupp.sum_fintype _ _ fun _ => rfl
    omega
  obtain ⟨j, hj⟩ := hex
  -- move it to position `0`
  have h1 : (rename (Equiv.swap j 0) f).coeff (Finsupp.mapDomain (Equiv.swap j 0) a) =
      f.coeff a := coeff_rename_mapDomain _ (Equiv.swap j 0).injective f a
  rw [hf (Equiv.swap j 0)] at h1
  have h0' : (Finsupp.mapDomain (Equiv.swap j 0) a) 0 = 0 := by
    rw [Finsupp.mapDomain_equiv_apply]
    simpa using hj
  have h2 := Finsupp.cons_tail (Finsupp.mapDomain (Equiv.swap j 0) a)
  rw [h0'] at h2
  rw [← h2, ← coeff_proj, h0, AddMonoidAlgebra.coeff_zero] at h1
  exact hne h1.symm

end Proj

/-! ## Homogeneous components and truncation -/

section Homog

variable {σ τ : Type*} {R : Type*} [CommRing R]

/-- A linear map which raises the degree of every monomial by `c` shifts homogeneous components
by `c`. -/
theorem homogeneousComponent_map (φ : MvPolynomial σ R →ₗ[R] MvPolynomial τ R) (c : ℕ)
    (hφ : ∀ (a : σ →₀ ℕ) (r : R), (φ (monomial a r)).IsHomogeneous (a.degree + c)) (i : ℕ)
    (f : MvPolynomial σ R) :
    homogeneousComponent (i + c) (φ f) = φ (homogeneousComponent i f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [homogeneousComponent_of_mem (hφ a r),
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    by_cases h : i = a.degree
    · simp [h]
    · simp [h]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem homogeneousComponent_map_lt (φ : MvPolynomial σ R →ₗ[R] MvPolynomial τ R) (c : ℕ)
    (hφ : ∀ (a : σ →₀ ℕ) (r : R), (φ (monomial a r)).IsHomogeneous (a.degree + c)) {i : ℕ}
    (hi : i < c) (f : MvPolynomial σ R) : homogeneousComponent i (φ f) = 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [homogeneousComponent_of_mem (hφ a r)]
    have h' : ¬ (i = a.degree + c) := by omega
    simp [h']
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]

variable (σ R) in
/-- The part of total degree `≤ D` of a polynomial. -/
def trunc (D : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  ∑ i ∈ range (D + 1), homogeneousComponent i

theorem trunc_apply (D : ℕ) (f : MvPolynomial σ R) :
    trunc σ R D f = ∑ i ∈ range (D + 1), homogeneousComponent i f := by
  simp [trunc, LinearMap.sum_apply]

theorem totalDegree_trunc_le (D : ℕ) (f : MvPolynomial σ R) :
    (trunc σ R D f).totalDegree ≤ D := by
  rw [trunc_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
  have := Finset.mem_range.mp hi
  exact ((homogeneousComponent_isHomogeneous i f).totalDegree_le).trans (by omega)

theorem trunc_of_totalDegree_le {D : ℕ} {f : MvPolynomial σ R} (h : f.totalDegree ≤ D) :
    trunc σ R D f = f := by
  rw [trunc_apply]
  conv_rhs => rw [← sum_homogeneousComponent f]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i _ hi => ?_
  exact homogeneousComponent_eq_zero _ _ (by simpa using hi)

theorem trunc_of_isHomogeneous {D m : ℕ} {f : MvPolynomial σ R} (h : f.IsHomogeneous m) :
    trunc σ R D f = if m ≤ D then f else 0 := by
  rw [trunc_apply]
  simp only [homogeneousComponent_of_mem h]
  rw [Finset.sum_ite_eq' (range (D + 1)) m (fun _ => f)]
  simp

/-- Truncation commutes with degree-shifting linear maps. -/
theorem trunc_map (φ : MvPolynomial σ R →ₗ[R] MvPolynomial τ R) (c : ℕ)
    (hφ : ∀ (a : σ →₀ ℕ) (r : R), (φ (monomial a r)).IsHomogeneous (a.degree + c)) (D : ℕ)
    (f : MvPolynomial σ R) : trunc τ R (D + c) (φ f) = φ (trunc σ R D f) := by
  rw [trunc_apply, trunc_apply, map_sum, show D + c + 1 = c + (D + 1) by omega,
    Finset.sum_range_add,
    Finset.sum_eq_zero (fun i hi => homogeneousComponent_map_lt φ c hφ (Finset.mem_range.mp hi) f),
    zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm c i, homogeneousComponent_map φ c hφ]

theorem trunc_rename (e : σ → τ) (D : ℕ) (f : MvPolynomial σ R) :
    trunc τ R D (rename e f) = rename e (trunc σ R D f) :=
  trunc_map (rename e).toLinearMap 0
    (fun _ r => (isHomogeneous_monomial r rfl).rename_isHomogeneous) D f

theorem trunc_isSymmetric (D : ℕ) {f : MvPolynomial σ R} (hf : f.IsSymmetric) :
    (trunc σ R D f).IsSymmetric := fun e => by rw [← trunc_rename, hf]

theorem pd_monomial_isHomogeneous (a : σ →₀ ℕ) (r : R) :
    (pdL σ R (monomial a r)).IsHomogeneous (a.degree + 1) := by
  classical
  change (pd σ R (monomial a r)).IsHomogeneous (a.degree + 1)
  rw [pd_monomial]
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  exact isHomogeneous_monomial _ (by rw [map_add, Finsupp.degree_single])

/-- `trunc (D + 1) ∘ d = d ∘ trunc D`. -/
theorem trunc_pd (D : ℕ) (f : MvPolynomial σ R) :
    trunc σ R (D + 1) (pd σ R f) = pd σ R (trunc σ R D f) :=
  trunc_map (pdL σ R) 1 pd_monomial_isHomogeneous D f

/-- `trunc (D + m) ∘ d^m = d^m ∘ trunc D`. -/
theorem trunc_pd_pow (D m : ℕ) (f : MvPolynomial σ R) :
    trunc σ R (D + m) ((pdL σ R ^ m) f) = (pdL σ R ^ m) (trunc σ R D f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← add_assoc]
    change trunc σ R (D + m + 1) (pd σ R ((pdL σ R ^ m) f)) = pd σ R _
    rw [trunc_pd, ih]

/-- `d` raises the total degree by at most one. -/
theorem totalDegree_pd_le (f : MvPolynomial σ R) :
    (pd σ R f).totalDegree ≤ f.totalDegree + 1 := by
  have h := trunc_pd f.totalDegree f
  rw [trunc_of_totalDegree_le le_rfl] at h
  rw [← h]
  exact totalDegree_trunc_le _ _

theorem totalDegree_pd_pow_le (m : ℕ) (f : MvPolynomial σ R) :
    ((pdL σ R ^ m) f).totalDegree ≤ f.totalDegree + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := totalDegree_pd_le ((pdL σ R ^ m) f)
    change (pd σ R ((pdL σ R ^ m) f)).totalDegree ≤ _
    omega

/-- In a domain, a quotient of homogeneous polynomials is homogeneous. -/
theorem isHomogeneous_of_mul [IsDomain R] {g f : MvPolynomial σ R} {a m : ℕ} (hg0 : g ≠ 0)
    (hg : g.IsHomogeneous a) (hgf : (g * f).IsHomogeneous (m + a)) : f.IsHomogeneous m := by
  have key : ∀ i, i ≠ m → homogeneousComponent i f = 0 := by
    intro i hi
    have h1 := homogeneousComponent_map (LinearMap.mulLeft R g) a
      (fun b r => by
        rw [add_comm]
        exact hg.mul (isHomogeneous_monomial r rfl)) i f
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, homogeneousComponent_of_mem hgf] at h1
    have h2 : ¬ (i + a = m + a) := by omega
    simp only [h2, ↓reduceIte] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hg0
  have h : f = homogeneousComponent m f := by
    conv_lhs => rw [← sum_homogeneousComponent f]
    by_cases hm : m ∈ range (f.totalDegree + 1)
    · exact Finset.sum_eq_single m (fun i _ hi => key i hi) (fun h => absurd hm h)
    · rw [Finset.sum_eq_zero fun i hi => key i fun h => hm (h ▸ hi)]
      exact (homogeneousComponent_eq_zero _ _ (by simpa using hm)).symm
  rw [h]
  exact homogeneousComponent_isHomogeneous m f

end Homog

/-! ## Truncation and the projection -/

section TruncProj

variable {R : Type*} [CommRing R] {n : ℕ}

theorem trunc_proj (D : ℕ) (f : MvPolynomial (Fin (n + 1)) R) :
    trunc (Fin n) R D (proj R n f) = proj R n (trunc (Fin (n + 1)) R D f) := by
  refine trunc_map (proj R n).toLinearMap 0 (fun a r => ?_) D f
  have h := (isHomogeneous_monomial (R := R) r (rfl : a.degree = a.degree)).aeval
    (projVar R n) (n := 1) fun i => by
      induction i using Fin.cases with
      | zero => rw [projVar_zero]; exact isHomogeneous_zero _ _ _
      | succ i => rw [projVar_succ]; exact isHomogeneous_X _ _
  rw [one_mul] at h
  exact h

end TruncProj

/-! ## Elementary and complete symmetric polynomials -/

section ElemComplete

variable {R : Type*} [CommRing R]

theorem multiset_esymm_zero_cons {S : Type*} [CommSemiring S] (s : Multiset S) (j : ℕ) :
    (0 ::ₘ s).esymm j = s.esymm j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
      Multiset.map_map, Multiset.esymm]
    have h : ∀ x ∈ Multiset.map (Multiset.prod ∘ Multiset.cons (0 : S))
        (Multiset.powersetCard j s), x = 0 := by
      intro x hx
      obtain ⟨t, -, rfl⟩ := Multiset.mem_map.mp hx
      simp
    rw [Multiset.sum_eq_zero h, add_zero]

/-- `e_j(0, x_1, …, x_n) = e_j(x_1, …, x_n)`. -/
theorem proj_esymm (n j : ℕ) : proj R n (esymm (Fin (n + 1)) R j) = esymm (Fin n) R j := by
  have h : (Finset.univ : Finset (Fin (n + 1))).val.map (projVar R n) =
      0 ::ₘ (Finset.univ : Finset (Fin n)).val.map X := by
    rw [Fin.univ_succ, Finset.cons_val, Finset.map_val, Multiset.map_cons, Multiset.map_map,
      projVar_zero]
    congr 1
  rw [proj, aeval_esymm_eq_multiset_esymm, h, multiset_esymm_zero_cons, esymm_eq_multiset_esymm]

theorem coeff_hsymm {σ : Type*} [Fintype σ] [DecidableEq σ] (j : ℕ) (b : σ →₀ ℕ) :
    (hsymm σ R j).coeff b = if b.degree = j then 1 else 0 := by
  rw [hsymm_eq_sum, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' ((univ : Finset σ).finsuppAntidiag j) b (fun _ => (1 : R))]
  simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Finsupp.degree_eq_sum]

/-- `h_j(0, x_1, …, x_n) = h_j(x_1, …, x_n)`. -/
theorem proj_hsymm (n j : ℕ) : proj R n (hsymm (Fin (n + 1)) R j) = hsymm (Fin n) R j := by
  ext b
  rw [coeff_proj, coeff_hsymm, coeff_hsymm]
  have h : (Finsupp.cons 0 b).degree = b.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero,
      zero_add]
    simp [Finsupp.cons_succ]
  rw [h]

theorem esymm_isHomogeneous {σ : Type*} [Fintype σ] (j : ℕ) :
    (esymm σ R j).IsHomogeneous j := by
  rw [esymm]
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have h := IsHomogeneous.prod t (fun i => (X i : MvPolynomial σ R)) (fun _ => 1)
    fun i _ => isHomogeneous_X R i
  rw [Finset.sum_const, smul_eq_mul, mul_one, (Finset.mem_powersetCard.mp ht).2] at h
  exact h

theorem hsymm_isHomogeneous {σ : Type*} [Fintype σ] [DecidableEq σ] (j : ℕ) :
    (hsymm σ R j).IsHomogeneous j := by
  rw [hsymm_eq_sum]
  refine IsHomogeneous.sum _ _ _ fun β hβ => ?_
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_sum]
  exact (Finset.mem_finsuppAntidiag.mp hβ).1

end ElemComplete

/-! ## Alternants and Schur polynomials -/

section Schur

variable {R : Type*} [CommRing R] {n : ℕ}

theorem xpow_isHomogeneous (β : Fin n → ℕ) :
    (xpow β : MvPolynomial (Fin n) R).IsHomogeneous (∑ i, β i) := by
  rw [xpow]
  exact IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow i (β i)

/-- The alternant `a_α` is homogeneous of degree `|α|`. -/
theorem alt_isHomogeneous (α : Fin n → ℕ) :
    (alt α : MvPolynomial (Fin n) R).IsHomogeneous (∑ i, α i) := by
  rw [alt_eq_antisymm, antisymm_apply]
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  exact (homogeneousSubmodule (Fin n) R _).smul_mem _ (xpow_isHomogeneous α).rename_isHomogeneous

theorem sum_lamDelta (lam : Fin n → ℕ) :
    ∑ i, lamDelta lam i = ∑ i, lam i + ∑ i, delta n i := by
  simp only [lamDelta, delta, Finset.sum_add_distrib]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl

/-- The Schur polynomial `s_λ` is homogeneous of degree `|λ|`. -/
theorem schur_isHomogeneous [IsDomain R] (lam : Fin n → ℕ) :
    (schur lam : MvPolynomial (Fin n) R).IsHomogeneous (∑ i, lam i) := by
  refine isHomogeneous_of_mul (alt_delta_ne_zero (R := R)) (alt_isHomogeneous (delta n)) ?_
  rw [schur, vandermonde_mul_schurA, ← sum_lamDelta]
  exact alt_isHomogeneous _

theorem proj_alt (α : Fin (n + 1) → ℕ) :
    proj R n (alt α) = (Matrix.of fun i j : Fin (n + 1) => projVar R n i ^ α j).det := by
  rw [alt, AlgHom.map_det]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, proj]

/-- Laplace expansion along the row of `x_0 = 0`. -/
theorem proj_alt_cons (β : Fin n → ℕ) :
    proj R n (alt (Fin.cons 0 fun j => β j + 1 : Fin (n + 1) → ℕ)) =
      (∏ i, X i) * alt β := by
  rw [proj_alt, Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · rw [alt, ← Matrix.det_mul_column]
    simp only [Fin.val_zero, pow_zero, one_mul, Matrix.of_apply, projVar_zero, Fin.cons_zero,
      Fin.succAbove_zero]
    congr 1
    ext i j
    simp [Matrix.submatrix_apply, pow_succ']
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp
  · simp

theorem proj_alt_of_pos {α : Fin (n + 1) → ℕ} (h : ∀ j, 0 < α j) : proj R n (alt α) = 0 := by
  rw [proj_alt]
  refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
  simp [(h j).ne']

theorem lamDelta_eq_cons {lam : Fin (n + 1) → ℕ} (h : lam (Fin.last n) = 0) :
    lamDelta lam = Fin.cons 0 fun j => lamDelta (fun i : Fin n => lam i.castSucc) j + 1 := by
  funext j
  induction j using Fin.cases with
  | zero => simp [lamDelta, h]
  | succ j => simp [lamDelta, Fin.rev_succ, add_assoc]

theorem delta_succ_eq_cons : delta (n + 1) = Fin.cons 0 fun j => delta n j + 1 := by
  funext j
  induction j using Fin.cases with
  | zero => simp [delta]
  | succ j => simp [delta]

theorem proj_alt_delta :
    proj R n (alt (delta (n + 1))) = (∏ i, X i) * alt (delta n) := by
  rw [delta_succ_eq_cons, proj_alt_cons]

theorem prod_X_ne_zero [IsDomain R] : (∏ i : Fin n, (X i : MvPolynomial (Fin n) R)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => X_ne_zero i

/-- **Stability of Schur polynomials**: `s_λ(x_1, …, x_n, 0) = s_λ(x_1, …, x_n)` if
`λ_{n+1} = 0`. -/
theorem proj_schur_of_last_eq_zero [IsDomain R] {lam : Fin (n + 1) → ℕ}
    (h : lam (Fin.last n) = 0) :
    proj R n (schur lam) = schur fun i : Fin n => lam i.castSucc := by
  have h1 := congrArg (proj R n) (vandermonde_mul_schurA (R := R) (lamDelta lam))
  rw [map_mul, proj_alt_delta] at h1
  conv_rhs at h1 => rw [lamDelta_eq_cons h, proj_alt_cons]
  rw [mul_assoc] at h1
  exact eq_schurA_of_mul (mul_left_cancel₀ prod_X_ne_zero h1)

/-- `s_λ(x_1, …, x_n, 0) = 0` if `λ_{n+1} ≠ 0`. -/
theorem proj_schur_of_last_ne_zero [IsDomain R] {lam : Fin (n + 1) → ℕ}
    (h : lam (Fin.last n) ≠ 0) : proj R n (schur lam) = 0 := by
  have hpos : ∀ j, 0 < lamDelta lam j := by
    intro j
    induction j using Fin.cases with
    | zero =>
      have h0 : lamDelta lam 0 = lam (Fin.last n) := by simp [lamDelta]
      rw [h0]
      exact Nat.pos_of_ne_zero h
    | succ j =>
      simp only [lamDelta, Fin.val_succ]
      omega
  have h1 := congrArg (proj R n) (vandermonde_mul_schurA (R := R) (lamDelta lam))
  rw [map_mul, proj_alt_delta, proj_alt_of_pos hpos] at h1
  exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero prod_X_ne_zero alt_delta_ne_zero)

end Schur

end

end OddMath.Frontier.EQPdg

import OddMath.Frontier.EQPdgHomotopy
import OddMath.Frontier.EQPdgSlash

/-!
# Slash cohomology of symmetric polynomials in characteristic `p`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2 (Theorem A.4).

Let `𝕜` be a field of characteristic `p > 0` and `Sym_n ⊆ 𝕜[x_1, …, x_n]` the symmetric
polynomials with the p-differential `d(x_i) = x_i²`. Under the bialternant isomorphism
`s_λ ↦ a_{λ+δ}` the differential becomes `D(a_α) = Σ_i (α_i - (n-1)) a_{α+e_i}`: a "bead"
at position `α_i` moves one step to the right with coefficient `α_i + 1 - n`, which vanishes
exactly when `α_i + 1 ≡ n (mod p)`. Hence the positions `ℕ` split into the *bottom block*
`[0, n mod p)` and the *full blocks* `[r + mp, r + mp + p)` (`r = n mod p`, `m ≥ 0`), and `D`
preserves the number `cnt m α` of beads in every block.

* If some full block contains a number of beads not divisible by `p` (`NT α`), the operator
  `T_b` of `EQPdgHomotopy` for the first such block gives a contracting homotopy
  (`sum_dAlt_pow_homotopy`).
* Otherwise every full block is empty or full, the bottom block is full, and `D(a_α) = 0`.

This file proves (`slash_sym_pos`, `slash_sym_zero_basis`): `H_{/k}(Sym_n) = 0` for
`1 ≤ k ≤ p - 2`, and the classes of the Schur polynomials `s_α` with `¬ NT α` form a basis of
`H_{/0}(Sym_n)`.
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset

noncomputable section

/-! ## Blocks and bead counts -/

/-- Bottom of the `m`-th full block: `(n mod p) + m p`. -/
def bot (n p m : ℕ) : ℕ := n % p + m * p

/-- The number of entries of `α` in the `m`-th full block `[bot m, bot m + p)`. -/
def cnt {n : ℕ} (p m : ℕ) (α : Fin n → ℕ) : ℕ :=
  (univ.filter (fun j => α j ∈ Ico (bot n p m) (bot n p m + p))).card

/-- The vector of block counts. -/
def cv {n : ℕ} (p : ℕ) (α : Fin n → ℕ) : ℕ → ℕ := fun m => cnt p m α

/-- A count vector is *non-trivial* if some full block count is not divisible by `p`. -/
def NTv (p : ℕ) (v : ℕ → ℕ) : Prop := ∃ m, ¬ p ∣ v m

theorem cnt_comp_perm {n : ℕ} (p m : ℕ) (α : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    cnt p m (α ∘ σ) = cnt p m α := by
  unfold cnt
  refine Finset.card_nbij' σ σ.symm ?_ ?_ ?_ ?_
  · intro j hj; simpa using hj
  · intro j hj; simpa using hj
  · intro j _; simp
  · intro j _; simp

theorem cv_comp_perm {n : ℕ} (p : ℕ) (α : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    cv p (α ∘ σ) = cv p α := funext fun m => cnt_comp_perm p m α σ

theorem mod_bot {n p : ℕ} (m : ℕ) : (bot n p m) % p = n % p := by
  rw [bot, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- Moving an entry `a ↦ a + 1` with `a + 1 ≢ n (mod p)` does not change block membership. -/
theorem mem_block_succ_iff {n p : ℕ} (m a : ℕ) (ha : (a + 1) % p ≠ n % p) :
    a + 1 ∈ Ico (bot n p m) (bot n p m + p) ↔ a ∈ Ico (bot n p m) (bot n p m + p) := by
  simp only [Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by omega⟩
    by_contra h
    have : a + 1 = bot n p m := by omega
    exact ha (this ▸ mod_bot m)
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, ?_⟩
    by_contra h
    have : a + 1 = bot n p m + p := by omega
    exact ha (by rw [this, Nat.add_mod_right, mod_bot m])

theorem cv_add_single {n p : ℕ} (α : Fin n → ℕ) (i : Fin n)
    (hi : (α i + 1) % p ≠ n % p) : cv p (α + Pi.single i 1) = cv p α := by
  funext m
  unfold cv cnt
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  by_cases hj : j = i
  · subst hj; simp only [Pi.single_eq_same]; exact mem_block_succ_iff m _ hi
  · simp [hj]

theorem mem_block_iff {n p : ℕ} (hp : 0 < p) (m x : ℕ) :
    x ∈ Ico (bot n p m) (bot n p m + p) ↔ n % p ≤ x ∧ (x - n % p) / p = m := by
  rw [Finset.mem_Ico, bot, Nat.div_eq_iff hp]
  generalize n % p = r
  generalize m * p = q
  omega

theorem mem_block_bot_iff {n p : ℕ} (hp : 0 < p) (m m' : ℕ) :
    bot n p m ∈ Ico (bot n p m') (bot n p m' + p) ↔ m = m' := by
  rw [mem_block_iff hp]
  constructor
  · rintro ⟨_, h⟩
    rw [bot, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hp] at h
    exact h
  · rintro rfl
    refine ⟨by rw [bot]; omega, ?_⟩
    rw [bot, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hp]

theorem mem_block_top_iff {n p : ℕ} (hp : 0 < p) (m m' : ℕ) :
    bot n p m + p - 1 ∈ Ico (bot n p m') (bot n p m' + p) ↔ m = m' := by
  rw [mem_block_iff hp]
  have h1 : bot n p m + p - 1 - n % p = (p - 1) + m * p := by rw [bot]; omega
  constructor
  · rintro ⟨_, h⟩
    rw [h1, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega), zero_add] at h
    exact h
  · rintro rfl
    refine ⟨by rw [bot]; omega, ?_⟩
    rw [h1, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]

section Field

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

omit hp in
theorem coeff_ne_zero_imp {n : ℕ} (a : ℕ) (h : ((a : ℕ) : k) - ((n : k) - 1) ≠ 0) :
    (a + 1) % p ≠ n % p := by
  intro h'
  apply h
  have : ((a + 1 : ℕ) : k) = (n : k) := (CharP.natCast_eq_natCast k p).mpr h'
  push_cast at this
  rw [← this]; ring

omit hp in
theorem bot_cast (n m : ℕ) : ((bot n p m : ℕ) : k) = (n : k) := by
  refine (CharP.natCast_eq_natCast k p).mpr ?_
  exact mod_bot m

end Field

section Homotopy

/-! ## Monomials with a fixed count vector -/

variable {k : Type*} [Field k] (p : ℕ) {n : ℕ}

/-- The span of the monomials `x^γ` with block-count vector `v`. -/
def Wv (v : ℕ → ℕ) : Submodule k (MvPolynomial (Fin n) k) :=
  Submodule.span k ((fun γ : Fin n →₀ ℕ => (monomial γ (1 : k) : MvPolynomial (Fin n) k)) ''
    {γ | cv p ⇑γ = v})

theorem monomial_mem_Wv (γ : Fin n →₀ ℕ) (c : k) :
    (monomial γ c : MvPolynomial (Fin n) k) ∈ Wv p (cv p ⇑γ) := by
  rw [show (monomial γ c : MvPolynomial (Fin n) k) = c • monomial γ 1 by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, rfl, rfl⟩)

theorem extOp_dOne_monomial (j : Fin n) (γ : Fin n →₀ ℕ) :
    extOp j (dOne n) (monomial γ 1 : MvPolynomial (Fin n) k) =
      (((γ j : ℕ) : k) - ((n : k) - 1)) • monomial (γ + Finsupp.single j 1) 1 := by
  rw [extOp_monomial, one_smul, dOne_X_pow, map_smul, mul_smul_comm, Polynomial.aeval_X_pow]
  congr 1
  rw [pow_succ, ← mul_assoc, show (monomial (Finsupp.erase j γ) 1 * X j ^ γ j :
      MvPolynomial (Fin n) k) = monomial γ 1 by
    rw [monomial_eq_erase_mul γ j, Polynomial.aeval_X_pow]]
  rw [show (X j : MvPolynomial (Fin n) k) = monomial (Finsupp.single j 1) 1 from rfl,
    monomial_mul_monomial, mul_one]

theorem dAlt_monomial (γ : Fin n →₀ ℕ) :
    dAlt (monomial γ 1 : MvPolynomial (Fin n) k) =
      ∑ j, (((γ j : ℕ) : k) - ((n : k) - 1)) • monomial (γ + Finsupp.single j 1) 1 := by
  rw [dAlt_eq_sum_extOp, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => extOp_dOne_monomial j γ

theorem dAlt_mem_Wv [CharP k p] {v : ℕ → ℕ} {f : MvPolynomial (Fin n) k} (hf : f ∈ Wv p v) :
    dAlt f ∈ Wv p v := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    rw [dAlt_monomial]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hc : ((γ j : ℕ) : k) - ((n : k) - 1) = 0
    · rw [hc, zero_smul]; exact Submodule.zero_mem _
    · have h := cv_add_single (p := p) (⇑γ) j (coeff_ne_zero_imp p _ hc)
      have := monomial_mem_Wv p (γ + Finsupp.single j 1) (1 : k)
      rw [Finsupp.coe_add, Finsupp.single_eq_pi_single, h, hγ] at this
      exact Submodule.smul_mem _ _ this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem dAlt_pow_mem_Wv [CharP k p] {v : ℕ → ℕ} {f : MvPolynomial (Fin n) k} (hf : f ∈ Wv p v) (i : ℕ) :
    (dAlt ^ i) f ∈ Wv p v := by
  induction i with
  | zero => simpa using hf
  | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact dAlt_mem_Wv p ih

theorem extOp_tOne_monomial (j : Fin n) (b : ℕ) (γ : Fin n →₀ ℕ) :
    extOp j (tOne p b) (monomial γ 1 : MvPolynomial (Fin n) k) =
      if γ j = b + p - 1 then monomial (Finsupp.erase j γ + Finsupp.single j b) 1 else 0 := by
  rw [extOp_monomial, one_smul, tOne_X_pow]
  split_ifs with h
  · rw [Polynomial.aeval_X_pow, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  · simp

theorem blockT_mem_Wv [hp : Fact p.Prime] (m : ℕ) {v : ℕ → ℕ} {f : MvPolynomial (Fin n) k} (hf : f ∈ Wv p v) :
    blockT p (bot n p m) f ∈ Wv p v := by
  have hp0 := hp.out.pos
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    rw [blockT, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [extOp_tOne_monomial]
    split_ifs with h
    · have := monomial_mem_Wv p (Finsupp.erase j γ + Finsupp.single j (bot n p m)) (1 : k)
      have hγ' : cv p ⇑γ = v := hγ
      rw [← hγ']
      convert this using 2
      funext m'
      unfold cv cnt
      congr 1
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hl : l = j
      · subst hl
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.erase_same, Finsupp.single_eq_same,
          zero_add, h]
        rw [mem_block_bot_iff hp0, mem_block_top_iff hp0]
      · simp [hl]
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-! ## The global homotopy -/

/-- The scalar `-1/cnt` for the first non-trivial block. -/
def scalv (v : ℕ → ℕ) (h : NTv p v) : k := -((Nat.cast (v (Nat.find h)) : k))⁻¹

open Classical in
/-- The homotopy `H`: on a monomial with non-trivial count vector it is `-(1/cnt) T_b` for the
first block `b` whose count is not divisible by `p`, and `0` otherwise. -/
def homotopyOp : Module.End k (MvPolynomial (Fin n) k) :=
  (basisMonomials (Fin n) k).constr k fun β =>
    if h : NTv p (cv p ⇑β) then scalv (k := k) p _ h • blockT p (bot n p (Nat.find h)) (monomial β 1)
    else 0

open Classical in
/-- The projection onto the monomials with non-trivial count vector. -/
def projNT : Module.End k (MvPolynomial (Fin n) k) :=
  (basisMonomials (Fin n) k).constr k fun β =>
    if NTv p (cv p ⇑β) then monomial β 1 else 0

open Classical in
theorem homotopyOp_of_mem_Wv {v : ℕ → ℕ} {f : MvPolynomial (Fin n) k} (hf : f ∈ Wv p v) :
    homotopyOp p f =
      if h : NTv p v then scalv (k := k) p v h • blockT p (bot n p (Nat.find h)) f else 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    subst hγ
    rw [homotopyOp]
    have := (basisMonomials (Fin n) k).constr_basis k (fun β =>
      if h : NTv p (cv p ⇑β) then scalv (k := k) p _ h • blockT p (bot n p (Nat.find h))
        (monomial β (1 : k)) else 0) γ
    rw [coe_basisMonomials] at this
    exact this
  | zero => split_ifs <;> simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]; split_ifs <;> simp
  | smul c x _ hx => rw [map_smul, hx]; split_ifs <;> simp [smul_comm c]

open Classical in
theorem projNT_of_mem_Wv {v : ℕ → ℕ} {f : MvPolynomial (Fin n) k} (hf : f ∈ Wv p v) :
    projNT p f = if NTv p v then f else 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    subst hγ
    rw [projNT]
    have := (basisMonomials (Fin n) k).constr_basis k (fun β =>
      if NTv p (cv p ⇑β) then (monomial β 1 : MvPolynomial (Fin n) k) else 0) γ
    rw [coe_basisMonomials] at this
    exact this
  | zero => split_ifs <;> simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]; split_ifs <;> simp
  | smul c x _ hx => rw [map_smul, hx]; split_ifs <;> simp

/-- **Global homotopy identity**: `Σ_{a+c=p-1} D^a H D^c = π_NT`, the projection onto the
monomials whose count vector is non-trivial. -/
theorem sum_dAlt_pow_homotopy [Fact p.Prime] [CharP k p] :
    ∑ a ∈ range p, (dAlt : Module.End k (MvPolynomial (Fin n) k)) ^ a * homotopyOp p *
      dAlt ^ (p - 1 - a) = projNT p := by
  classical
  refine (basisMonomials (Fin n) k).ext fun β => ?_
  simp only [coe_basisMonomials]
  have hm := monomial_mem_Wv p β (1 : k)
  set v := cv p ⇑β with hv
  rw [LinearMap.sum_apply, projNT_of_mem_Wv p hm]
  have hH : ∀ a, (homotopyOp p) ((dAlt ^ (p - 1 - a)) (monomial β 1)) =
      if h : NTv p v then scalv (k := k) p v h • blockT p (bot n p (Nat.find h))
        ((dAlt ^ (p - 1 - a)) (monomial β (1 : k))) else 0 :=
    fun a => homotopyOp_of_mem_Wv p (dAlt_pow_mem_Wv p hm _)
  simp only [Module.End.mul_apply, hH]
  by_cases h : NTv p v
  · simp only [h, ↓reduceDIte, ↓reduceIte, map_smul]
    rw [← Finset.smul_sum]
    have hsum := congrArg (fun F : Module.End k (MvPolynomial (Fin n) k) => F (monomial β 1))
      (sum_dAlt_pow_blockT (k := k) (n := n) p (bot_cast (k := k) p n (Nat.find h)))
    simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.neg_apply] at hsum
    rw [hsum, blockN_monomial, scalv]
    have hne : ((v (Nat.find h) : ℕ) : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k p]
      exact Nat.find_spec h
    have hcnt : ((univ.filter (fun j => β j ∈ Ico (bot n p (Nat.find h))
        (bot n p (Nat.find h) + p))).card : k) = ((v (Nat.find h) : ℕ) : k) := rfl
    rw [hcnt, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hne]
    simp
  · simp only [h, ↓reduceDIte, ↓reduceIte, map_zero, Finset.sum_const_zero]

theorem rename_mem_Wv (σ : Equiv.Perm (Fin n)) (β : Fin n →₀ ℕ) :
    (rename σ (monomial β 1) : MvPolynomial (Fin n) k) ∈ Wv p (cv p ⇑β) := by
  rw [rename_monomial]
  have := monomial_mem_Wv p (Finsupp.mapDomain σ β) (1 : k)
  convert this using 2
  have : ⇑(Finsupp.mapDomain σ β) = ⇑β ∘ σ.symm := by
    funext j
    obtain ⟨j', rfl⟩ := σ.surjective j
    simp [Finsupp.mapDomain_apply_of_injective σ.injective]
  rw [this, cv_comp_perm]

theorem homotopyOp_rename (σ : Equiv.Perm (Fin n)) (f : MvPolynomial (Fin n) k) :
    homotopyOp p (rename σ f) = rename σ (homotopyOp p f) := by
  classical
  have key : (homotopyOp p).comp (rename σ).toLinearMap =
      (rename σ).toLinearMap.comp (homotopyOp (k := k) (n := n) p) := by
    refine (basisMonomials (Fin n) k).ext fun β => ?_
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [homotopyOp_of_mem_Wv p (rename_mem_Wv p σ β),
      homotopyOp_of_mem_Wv p (monomial_mem_Wv p β 1)]
    split_ifs with h
    · rw [map_smul, rename_blockT]
    · simp
  exact LinearMap.congr_fun key f

theorem projNT_rename (σ : Equiv.Perm (Fin n)) (f : MvPolynomial (Fin n) k) :
    projNT p (rename σ f) = rename σ (projNT p f) := by
  classical
  have key : (projNT p).comp (rename σ).toLinearMap =
      (rename σ).toLinearMap.comp (projNT (k := k) (n := n) p) := by
    refine (basisMonomials (Fin n) k).ext fun β => ?_
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [projNT_of_mem_Wv p (rename_mem_Wv p σ β), projNT_of_mem_Wv p (monomial_mem_Wv p β 1)]
    split_ifs <;> simp
  exact LinearMap.congr_fun key f

theorem projNT_alt {α : Fin n → ℕ} (hα : NTv p (cv p α)) :
    projNT p (alt α : MvPolynomial (Fin n) k) = alt α := by
  classical
  rw [alt_eq_antisymm, antisymm_comm _ (projNT_rename p), xpow_eq_monomial]
  have := monomial_mem_Wv p (Finsupp.equivFunOnFinite.symm α) (1 : k)
  rw [projNT_of_mem_Wv p this]
  simp only [Finsupp.coe_equivFunOnFinite_symm] at *
  simp [hα]

end Homotopy

/-! ## Combinatorics of trivial count vectors -/

section Comb

variable {n : ℕ} (p : ℕ)

/-- If every full block count is divisible by `p` (and the entries are distinct), then each
bead that can move (`α_i + 1 ≢ n mod p`) is blocked by another bead at `α_i + 1`. -/
theorem exists_eq_succ_of_trivial (hp0 : 0 < p) {α : Fin n → ℕ} (hinj : Function.Injective α)
    (htriv : ¬ NTv p (cv p α)) (i : Fin n) (hi : (α i + 1) % p ≠ n % p) :
    ∃ j, α j = α i + 1 := by
  by_contra hne
  simp only [not_exists] at hne
  have hdiv : ∀ m, p ∣ cnt p m α := fun m => by
    by_contra h; exact htriv ⟨m, h⟩
  have hr : n % p < p := Nat.mod_lt _ hp0
  by_cases hge : n % p ≤ α i
  · set m := (α i - n % p) / p
    have hmem : α i ∈ Ico (bot n p m) (bot n p m + p) := (mem_block_iff hp0 m (α i)).mpr ⟨hge, rfl⟩
    have hmem' : α i + 1 ∈ Ico (bot n p m) (bot n p m + p) :=
      (mem_block_succ_iff m (α i) hi).mpr hmem
    have hle : cnt p m α ≤ p - 1 := by
      unfold cnt
      calc _ ≤ ((Ico (bot n p m) (bot n p m + p)).erase (α i + 1)).card := by
            refine Finset.card_le_card_of_injOn α ?_ hinj.injOn
            intro j hj
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
            simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
            exact ⟨hj, hne j⟩
        _ = p - 1 := by rw [Finset.card_erase_of_mem hmem', Nat.card_Ico]; omega
    have hpos : 0 < cnt p m α := Finset.card_pos.mpr ⟨i, by simpa using hmem⟩
    obtain ⟨c, hc⟩ := hdiv m
    rcases c with _ | c
    · omega
    · have : p ≤ p * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · have hlt : α i + 1 < n % p := by
      by_contra h
      have h' : α i + 1 = n % p := by omega
      apply hi
      rw [h', Nat.mod_mod]
    -- the entries below `n mod p`
    set L := univ.filter (fun j => α j < n % p)
    set G := univ.filter (fun j => ¬ α j < n % p)
    have hLG : L.card + G.card = n := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have hG : p ∣ G.card := by
      set M := univ.sup α + 1
      rw [Finset.card_eq_sum_card_fiberwise (f := fun j => (α j - n % p) / p) (t := range M)]
      · refine Finset.dvd_sum fun m _ => ?_
        convert hdiv m using 1
        unfold cnt
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, G, mem_block_iff hp0, not_lt]
      · intro j _
        simp only [Finset.coe_range, Set.mem_Iio]
        have : α j ≤ univ.sup α := Finset.le_sup (Finset.mem_univ j)
        have : (α j - n % p) / p ≤ α j := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
        omega
    have hL : L.card ≤ n % p - 1 := by
      calc L.card ≤ ((range (n % p)).erase (α i + 1)).card := by
            refine Finset.card_le_card_of_injOn α ?_ hinj.injOn
            intro j hj
            simp only [L, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
            simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Finset.mem_range,
              Set.mem_singleton_iff]
            exact ⟨hj, hne j⟩
        _ = n % p - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hlt), Finset.card_range]
    obtain ⟨g, hg⟩ := hG
    have hmod : L.card % p = n % p := by
      have h' : (L.card + G.card) % p = n % p := by rw [hLG]
      rwa [hg, Nat.add_mul_mod_self_left] at h'
    rw [Nat.mod_eq_of_lt (by omega)] at hmod
    omega

theorem strictMono_add_single {α : Fin n → ℕ} (hα : StrictMono α) (i : Fin n)
    (hinj : Function.Injective (α + Pi.single i 1)) : StrictMono (α + Pi.single i 1) := by
  intro a b hab
  have hne := hinj.ne (ne_of_lt hab)
  have hlt := hα hab
  simp only [Pi.add_apply, Pi.single_apply] at hne ⊢
  split_ifs at hne ⊢ with ha hb hb
  · subst ha; subst hb; exact absurd hab (lt_irrefl _)
  · subst ha; omega
  · subst hb; omega
  · omega

end Comb

/-! ## Symmetric polynomials -/

section Sym

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] {n : ℕ}

/-- The differential `d` restricted to `Sym_n`. -/
def dSym : Module.End k (SymSub : Submodule k (MvPolynomial (Fin n) k)) :=
  (pdL (Fin n) k).restrict fun _ hf => mem_SymSub.mpr (pd_isSymmetric (mem_SymSub.mp hf))

omit hp [CharP k p] in
theorem dSym_apply (f : (SymSub : Submodule k (MvPolynomial (Fin n) k))) :
    (dSym f).1 = pd (Fin n) k f.1 := rfl

omit hp [CharP k p] in
theorem symToAlt_dSym_pow (m : ℕ) (f : (SymSub : Submodule k (MvPolynomial (Fin n) k))) :
    (symToAlt ((dSym ^ m) f)).1 = (dAlt ^ m) (symToAlt f).1 := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, symToAlt_apply,
      symToAlt_apply, dSym_apply, dAlt_vandermonde_mul]

/-- The Schur indices with a non-trivial count vector. -/
def ntSet : Set {α : Fin n → ℕ // StrictMono α} := {α | NTv p (cv p α.1)}

/-- `T`: the span of the `s_α` with trivial count vector. -/
def symT : Submodule k (SymSub : Submodule k (MvPolynomial (Fin n) k)) :=
  Submodule.span k (Set.range fun α : ↥(ntSet (n := n) p)ᶜ => schurBasis α.1)

/-- `F`: the span of the `s_α` with non-trivial count vector. -/
def symF : Submodule k (SymSub : Submodule k (MvPolynomial (Fin n) k)) :=
  Submodule.span k (Set.range fun α : ↥(ntSet (n := n) p) => schurBasis α.1)

omit hp [CharP k p] in
theorem isCompl_symT_symF : IsCompl (symT (k := k) (n := n) p) (symF p) := by
  have := (schurBasis (R := k) (n := n)).linearIndependent.isCompl_span_image
    (schurBasis (R := k) (n := n)).span_eq (isCompl_compl (x := ntSet (n := n) p)).symm
  rw [Set.image_eq_range, Set.image_eq_range] at this
  exact this

theorem symT_le_ker : symT (k := k) (n := n) p ≤ LinearMap.ker (dSym (k := k) (n := n)) := by
  rw [symT, Submodule.span_le]
  rintro _ ⟨⟨α, hα⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  apply Subtype.ext
  rw [dSym_apply, schurBasis_apply, pd_schurA, Submodule.coe_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hc : ((α.1 i : ℕ) : k) - ((n : k) - 1) = 0
  · rw [hc, zero_smul]
  · rw [schurA_eq_zero_of_not_injective, smul_zero]
    obtain ⟨j, hj⟩ := exists_eq_succ_of_trivial p hp.out.pos α.2.injective hα i
      (coeff_ne_zero_imp p _ hc)
    have hji : j ≠ i := by intro h; subst h; omega
    intro hinj
    apply hji
    apply hinj
    simp [hji, hj]

omit hp in
theorem symF_map_le : (symF (k := k) (n := n) p).map (dSym (k := k) (n := n)) ≤ symF p := by
  rw [Submodule.map_le_iff_le_comap, symF, Submodule.span_le]
  rintro _ ⟨⟨α, hα⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  let y : Fin n → (SymSub : Submodule k (MvPolynomial (Fin n) k)) := fun i =>
    ⟨schurA (α.1 + Pi.single i 1), mem_SymSub.mpr (schurA_isSymmetric _)⟩
  have hdecomp : dSym (schurBasis α) =
      ∑ i, (((α.1 i : ℕ) : k) - ((n : k) - 1)) • y i := by
    apply Subtype.ext
    rw [dSym_apply, schurBasis_apply, pd_schurA, Submodule.coe_sum]
    rfl
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hc : ((α.1 i : ℕ) : k) - ((n : k) - 1) = 0
  · rw [hc, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ ?_
    by_cases hinj : Function.Injective (α.1 + Pi.single i 1)
    · have hmono := strictMono_add_single α.2 i hinj
      have hcv := cv_add_single (p := p) α.1 i (coeff_ne_zero_imp p _ hc)
      have : y i = schurBasis ⟨_, hmono⟩ := by
        apply Subtype.ext; rw [schurBasis_apply]
      rw [this]
      refine Submodule.subset_span ⟨⟨⟨_, hmono⟩, ?_⟩, rfl⟩
      show NTv p (cv p (α.1 + Pi.single i 1))
      rw [hcv]; exact hα
    · have : y i = 0 := by
        apply Subtype.ext; exact schurA_eq_zero_of_not_injective hinj
      rw [this]; exact Submodule.zero_mem _

omit hp [CharP k p] in
theorem homotopyOp_mem_Alt {x : MvPolynomial (Fin n) k} (hx : x ∈ Alt) :
    homotopyOp p x ∈ (Alt : Submodule k (MvPolynomial (Fin n) k)) :=
  antisymm_mem_Alt_of_comm _ (homotopyOp_rename p) hx

/-- The homotopy transported to `Sym_n`. -/
def homotopySym : Module.End k (SymSub : Submodule k (MvPolynomial (Fin n) k)) :=
  symToAlt.symm.toLinearMap ∘ₗ ((homotopyOp p).restrict fun _ hx => homotopyOp_mem_Alt p hx) ∘ₗ
    symToAlt.toLinearMap

omit hp [CharP k p] in
theorem symToAlt_homotopySym (f : (SymSub : Submodule k (MvPolynomial (Fin n) k))) :
    (symToAlt (homotopySym p f)).1 = homotopyOp p (symToAlt f).1 := by
  simp [homotopySym]

omit hp [CharP k p] in
theorem projNT_symToAlt_of_mem_symF {v : (SymSub : Submodule k (MvPolynomial (Fin n) k))}
    (hv : v ∈ symF p) : projNT p (symToAlt v).1 = (symToAlt v).1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨α, hα⟩, rfl⟩ := hx
    rw [symToAlt_apply, schurBasis_apply, vandermonde_mul_schurA]
    exact projNT_alt p hα
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, Submodule.coe_smul, hx]

theorem symF_homotopy {v : (SymSub : Submodule k (MvPolynomial (Fin n) k))} (hv : v ∈ symF p) :
    v = ∑ a ∈ range p, (dSym ^ a) (homotopySym p ((dSym ^ (p - 1 - a)) v)) := by
  apply symToAlt.injective
  apply Subtype.ext
  rw [map_sum, Submodule.coe_sum]
  simp only [symToAlt_dSym_pow, symToAlt_homotopySym]
  have := congrArg (fun F : Module.End k (MvPolynomial (Fin n) k) => F (symToAlt v).1)
    (sum_dAlt_pow_homotopy (k := k) (n := n) p)
  simp only [LinearMap.sum_apply, Module.End.mul_apply] at this
  rw [this, projNT_symToAlt_of_mem_symF p hv]

/-- **Ellis–Qi, Theorem A.4 (1), vanishing part** (in `n` variables): `H_{/j}(Sym_n) = 0` for
`1 ≤ j ≤ p - 2`. -/
theorem slash_sym_pos (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ p - 2) :
    Subsingleton (SlashCohomology (dSym (k := k) (n := n)) p j) :=
  (slash_of_isCompl dSym p hp.out.two_le (symT p) (symF p) (isCompl_symT_symF p)
    (symT_le_ker p) (symF_map_le p) (fun j _ hjp v hv hdv =>
      mem_range_of_homotopy dSym (homotopySym p) p j (by omega) v (symF_homotopy p hv)
        hdv)).1 j hj1 hj2

/-- Exactness of `F`: `Ker(d^j) ∩ F ⊆ Im(d^{p-j})`. -/
theorem symF_exact : ∀ j, 1 ≤ j → j ≤ p - 1 → ∀ v ∈ symF (k := k) (n := n) p,
    (dSym ^ j) v = 0 → v ∈ LinearMap.range (dSym ^ (p - j)) :=
  fun j _ hjp v hv hdv =>
    mem_range_of_homotopy dSym (homotopySym p) p j (by omega) v (symF_homotopy p hv) hdv

theorem symT_mem_ker (t : symT (k := k) (n := n) p) : (dSym ^ (0 + 1)) t.1 = 0 := by
  have := symT_le_ker p t.2; simpa using this

/-- The class map `T → H_{/0}(Sym_n)`. -/
def classT : symT (k := k) (n := n) p →ₗ[k] SlashCohomology (dSym (k := k) (n := n)) p 0 :=
  (Submodule.mkQ _) ∘ₗ ((symT p).subtype.codRestrict (LinearMap.ker (dSym ^ (0 + 1)))
    (fun t => symT_mem_ker p t))

theorem classT_apply (t : symT (k := k) (n := n) p) :
    classT p t = slashClass dSym p 0 t.1 (symT_mem_ker p t) := rfl

theorem classT_bijective : Function.Bijective (classT (k := k) (n := n) p) := by
  have hbij := (slash_of_isCompl (dSym (k := k) (n := n)) p hp.out.two_le (symT p) (symF p)
    (isCompl_symT_symF p) (symT_le_ker p) (symF_map_le p) (symF_exact p)).2
  convert hbij using 1
  funext t
  rfl

omit hp [CharP k p] in
theorem linearIndependent_schur_trivial :
    LinearIndependent k (fun α : ↥(ntSet (n := n) p)ᶜ => schurBasis (R := k) α.1) :=
  (schurBasis (R := k) (n := n)).linearIndependent.comp _ Subtype.val_injective

/-- The basis `{[s_α] : α trivial}` of `H_{/0}(Sym_n)`. -/
def h0Basis : Module.Basis ↥(ntSet (n := n) p)ᶜ k (SlashCohomology (dSym (k := k) (n := n)) p 0) :=
  (Module.Basis.span (linearIndependent_schur_trivial p)).map
    (LinearEquiv.ofBijective (classT p) (classT_bijective p))

theorem h0Basis_apply (α : ↥(ntSet (n := n) p)ᶜ) :
    h0Basis (k := k) p α = classT p ⟨schurBasis α.1, Submodule.subset_span ⟨α, rfl⟩⟩ := by
  rw [h0Basis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
  congr 1
  apply Subtype.ext
  rw [Module.Basis.span_apply]

/-- **Ellis–Qi, Theorem A.4 (1), degree zero** (in `n` variables): the classes of the Schur
polynomials `s_α` with trivial count vector (every full block empty or full; see
`EQPdgLimaPart` for the translation to `p`-Lima partitions) form a basis of
`H_{/0}(Sym_n)`. -/
theorem slash_sym_zero_basis :
    ∃ b : Module.Basis ↥(ntSet (n := n) p)ᶜ k (SlashCohomology (dSym (k := k) (n := n)) p 0),
      ∀ α, b α = slashClass dSym p 0 (schurBasis (R := k) α.1)
        ((symT_le_ker p) (Submodule.subset_span ⟨α, rfl⟩) |> fun h => by simpa using h) :=
  ⟨h0Basis p, fun α => by rw [h0Basis_apply, classT_apply]⟩

end Sym

end

end OddMath.Frontier.EQPdg

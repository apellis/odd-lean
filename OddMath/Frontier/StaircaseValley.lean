import OddMath.Frontier.StaircaseSorting
import OddMath.Frontier.PrefixEmbedding
import OddMath.Frontier.MonomialReversal
import OddMath.Frontier.BoxComplement

/-! # Evaluating the longest odd divided difference on valley monomials

EKL arXiv:1111.1320v1, §4.3.1, Props 4.6–4.7 and the top-degree part of Lemma 4.9, pp. 36–37.

A *valley* exponent vector strictly decreases up to a split point `k` and strictly increases
after it.  In the top degree `binom(N,2)`, `D_N(x^γ)` is a constant, equal to `0` unless the
entries of `γ` are distinct, and then to `(-1)^(binom(N,3) + Σ_{j ≥ k} binom(γ_j, 3))`.

The proof peels the maximal exponent, which sits at an end of the valley:
`D_N(x_1^{N-1} x^{γ'}) = (-1)^{binom(N-1,2)} D_{N-1}(x^{γ'})` and
`D_N(x^{γ'} x_N^{N-1}) = (-1)^{binom(N,3)} D_{N-1}(x^{γ'})`.  The peeling constants come from
reduced-word factorizations of `D_N`, and are pinned down by the staircase (Lemma 2.10) and
the increasing staircase (Prop 4.7).  A maximum `≥ N` kills by degree; a maximum `≤ N−2`
kills by the sorting lemma. -/
namespace OddMath.Frontier.StaircaseValley
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
open LongestDivided LongestFactor PrefixEmbedding
open scoped BigOperators

/-! ## Constants -/

theorem smul_one_apply_zero {N : ℕ} (r : ℤ) : (r • (1 : SkewPolynomial N)) 0 = r := by
  change (r • Finsupp.single (0 : Fin N → ℕ) (1 : ℤ)) 0 = r
  simp

theorem smul_one_injective {N : ℕ} {r s : ℤ} (h : r • (1 : SkewPolynomial N) = s • 1) :
    r = s := by
  have := congrArg (fun f : SkewPolynomial N => f 0) h
  simp only at this
  rwa [smul_one_apply_zero, smul_one_apply_zero] at this

/-- The value of `D_N` on a top-degree monomial. -/
noncomputable def top (N : ℕ) (γ : Fin N → ℕ) : ℤ := D N (monomial γ 1) 0

theorem D_eq_top {N : ℕ} {γ : Fin N → ℕ} (h : ∑ j, γ j = N.choose 2) :
    D N (monomial γ 1) = top N γ • 1 :=
  D_monomial_top_degree N γ 1 h

theorem sum_staircase (N : ℕ) : ∑ i : Fin N, (N-1-i.val) = N.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N-1-i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id, Nat.choose_two_right]

theorem top_staircase (N : ℕ) : top N (fun i => N-1-i.val) = (-1 : ℤ)^(N.choose 3) := by
  have h := D_staircase N
  rw [staircase, D_eq_top (sum_staircase N)] at h
  exact smul_one_injective h

theorem top_increasing (N : ℕ) :
    top N (fun i => i.val) = (-1 : ℤ)^(N.choose 3 + N.choose 4) := by
  have h := MonomialReversal.D_increasing_staircase N
  rw [D_eq_top (BoxComplement.sum_val_fin N)] at h
  exact smul_one_injective h

/-! ## Peeling the first variable -/

theorem shiftedWord_eq (n : ℕ) : shiftedWord n = (wordIn n (n+2) le_rfl).map Fin.succ := rfl

theorem gen_zero_pow (n e : ℕ) :
    generator (0 : Fin (n+3)) ^ e = monomial (Fin.cons e 0) 1 := by
  have h1 : (monomial (0 : Fin (n+2) → ℕ) 1 : SkewPolynomial (n+2)) = 1 := rfl
  rw [monomial_cons, h1, map_one, mul_one]

theorem left_peel_apply (n e : ℕ) (γ' : Fin (n+2) → ℕ) (ε : ℤ)
    (hD : D (n+3) = ε • (applyWord (leftPeelWord n) ∘ₗ applyWord (shiftedWord n))) :
    D (n+3) (monomial (Fin.cons e γ') 1) =
      (ε * (-1 : ℤ)^(e * (n+2).choose 2)) •
        applyWord (leftPeelWord n) (generator 0 ^ e * shiftHom (n+2) (D (n+2) (monomial γ' 1))) := by
  rw [hD, LinearMap.smul_apply, LinearMap.comp_apply, shiftedWord_eq, D_shift_monomial,
    map_zsmul, smul_smul]

theorem left_peel_low (n e : ℕ) (γ' : Fin (n+2) → ℕ) (h : ∑ j, γ' j < (n+2).choose 2) :
    D (n+3) (monomial (Fin.cons e γ') 1) = 0 := by
  obtain ⟨ε, -, hD⟩ := D_factor_left_peel n
  rw [left_peel_apply n e γ' ε hD, D_monomial_low_degree _ _ _ h,
    show generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) 0 = 0 by rw [map_zero]; exact OddMath.SkewPolynomial.mul_zero _,
    map_zero, smul_zero]

theorem left_peel_exists (n : ℕ) : ∃ κ : ℤ, ∀ γ' : Fin (n+2) → ℕ,
    ∑ j, γ' j = (n+2).choose 2 → top (n+3) (Fin.cons (n+2) γ') = κ * top (n+2) γ' := by
  obtain ⟨ε, -, hD⟩ := D_factor_left_peel n
  have hlen : (leftPeelWord n).length = n+2 := by simp [leftPeelWord]
  have hsum : ∑ j, (Fin.cons (n+2) (0 : Fin (n+2) → ℕ) : Fin (n+3) → ℕ) j = n+2 := by
    simp [Fin.sum_univ_succ]
  set t := applyWord (leftPeelWord n) (monomial (Fin.cons (n+2) 0) 1) 0
  refine ⟨ε * (-1 : ℤ)^((n+2) * (n+2).choose 2) * t, fun γ' hγ' => ?_⟩
  have h := left_peel_apply n (n+2) γ' ε hD
  rw [D_eq_top hγ', shiftHom_const, mul_smul_comm, mul_one, map_zsmul, gen_zero_pow,
    applyWord_monomial_top _ _ _ (by rw [hsum, hlen]), smul_smul, smul_smul] at h
  rw [top, h, smul_one_apply_zero]
  ring

theorem cons_staircase (n : ℕ) :
    (Fin.cons (n+2) (fun i : Fin (n+2) => n+2-1-i.val) : Fin (n+3) → ℕ) =
      fun i => n+3-1-i.val := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Fin.cons_succ, Fin.val_succ]; omega

/-- Peeling a maximal first exponent: `D_N(x_1^{N−1} x^{γ'}) = (-1)^{binom(N−1,2)} D_{N−1}(x^{γ'})`. -/
theorem left_peel (n : ℕ) (γ' : Fin (n+2) → ℕ) (h : ∑ j, γ' j = (n+2).choose 2) :
    top (n+3) (Fin.cons (n+2) γ') = (-1 : ℤ)^((n+2).choose 2) * top (n+2) γ' := by
  obtain ⟨κ, hκ⟩ := left_peel_exists n
  have hδ := hκ _ (sum_staircase (n+2))
  rw [cons_staircase, top_staircase, top_staircase] at hδ
  have hκv : κ = (-1 : ℤ)^((n+2).choose 2) := by
    have e3 : (n+3).choose 3 = (n+2).choose 2 + (n+2).choose 3 := Nat.choose_succ_succ' _ _
    rw [e3, pow_add] at hδ
    exact (mul_right_cancel₀ (pow_ne_zero _ (by norm_num)) hδ).symm
  rw [hκ γ' h, hκv]

/-! ## Peeling the last variable -/

theorem gen_last_pow (n e : ℕ) :
    generator (Fin.last (n+2)) ^ e = monomial (Fin.snoc (0 : Fin (n+2) → ℕ) e) 1 := by
  have h1 : (monomial (0 : Fin (n+2) → ℕ) 1 : SkewPolynomial (n+2)) = 1 := rfl
  rw [monomial_snoc, h1, map_one, one_mul]

theorem right_peel_apply (n e : ℕ) (γ' : Fin (n+2) → ℕ) (ε : ℤ)
    (hD : D (n+3) = ε • (applyWord (rightPeelWord n) ∘ₗ applyWord (wordIn (n+1) (n+2) (by omega)))) :
    D (n+3) (monomial (Fin.snoc γ' e) 1) =
      ε • applyWord (rightPeelWord n)
        (prefixHom (n+2) (D (n+2) (monomial γ' 1)) * generator (Fin.last (n+2)) ^ e) := by
  rw [hD, LinearMap.smul_apply, LinearMap.comp_apply, D_prefix_monomial]

theorem right_peel_low (n e : ℕ) (γ' : Fin (n+2) → ℕ) (h : ∑ j, γ' j < (n+2).choose 2) :
    D (n+3) (monomial (Fin.snoc γ' e) 1) = 0 := by
  obtain ⟨ε, -, hD⟩ := D_factor_right_peel n
  rw [right_peel_apply n e γ' ε hD, D_monomial_low_degree _ _ _ h,
    show prefixHom (n+2) 0 * generator (Fin.last (n+2)) ^ e = 0 by rw [map_zero]; exact OddMath.SkewPolynomial.zero_mul _,
    map_zero, smul_zero]

theorem right_peel_exists (n : ℕ) : ∃ κ : ℤ, ∀ γ' : Fin (n+2) → ℕ,
    ∑ j, γ' j = (n+2).choose 2 → top (n+3) (Fin.snoc γ' (n+2)) = κ * top (n+2) γ' := by
  obtain ⟨ε, -, hD⟩ := D_factor_right_peel n
  have hlen : (rightPeelWord n).length = n+2 := by simp [rightPeelWord]
  have hsum : ∑ j, (Fin.snoc (0 : Fin (n+2) → ℕ) (n+2) : Fin (n+3) → ℕ) j = n+2 := by
    simp [Fin.sum_univ_castSucc]
  set t := applyWord (rightPeelWord n) (monomial (Fin.snoc (0 : Fin (n+2) → ℕ) (n+2)) 1) 0
  refine ⟨ε * t, fun γ' hγ' => ?_⟩
  have h := right_peel_apply n (n+2) γ' ε (by exact hD)
  rw [D_eq_top hγ', prefixHom_const, smul_mul_assoc, one_mul, map_zsmul, gen_last_pow,
    applyWord_monomial_top _ _ _ (by rw [hsum, hlen]), smul_smul, smul_smul] at h
  rw [top, h, smul_one_apply_zero]
  ring

theorem snoc_increasing (n : ℕ) :
    (Fin.snoc (fun i : Fin (n+2) => i.val) (n+2) : Fin (n+3) → ℕ) = fun i => i.val := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · simp

/-- Peeling a maximal last exponent: `D_N(x^{γ'} x_N^{N−1}) = (-1)^{binom(N,3)} D_{N−1}(x^{γ'})`. -/
theorem right_peel (n : ℕ) (γ' : Fin (n+2) → ℕ) (h : ∑ j, γ' j = (n+2).choose 2) :
    top (n+3) (Fin.snoc γ' (n+2)) = (-1 : ℤ)^((n+3).choose 3) * top (n+2) γ' := by
  obtain ⟨κ, hκ⟩ := right_peel_exists n
  have hδ := hκ _ (BoxComplement.sum_val_fin (n+2))
  rw [snoc_increasing, top_increasing, top_increasing] at hδ
  have hκv : κ = (-1 : ℤ)^((n+3).choose 3) := by
    have e4 : (n+3).choose 4 = (n+2).choose 3 + (n+2).choose 4 := Nat.choose_succ_succ' _ _
    rw [e4, pow_add (-1 : ℤ) ((n+3).choose 3)] at hδ
    exact (mul_right_cancel₀ (pow_ne_zero _ (by norm_num)) hδ).symm
  rw [hκ γ' h, hκv]


/-! ## Valleys -/

/-- `γ` strictly decreases on indices `< k` and strictly increases on indices `≥ k`. -/
def IsValley {N : ℕ} (γ : Fin N → ℕ) (k : ℕ) : Prop :=
  (∀ i j : Fin N, i < j → j.val < k → γ j < γ i) ∧ (∀ i j : Fin N, i < j → k ≤ i.val → γ i < γ j)

/-- `Σ_{j ≥ k} binom(γ_j, 3)`: the sign exponent contributed by the increasing arm. -/
def armSum {N : ℕ} (γ : Fin N → ℕ) (k : ℕ) : ℕ :=
  ∑ j : Fin N, if k ≤ j.val then (γ j).choose 3 else 0

theorem IsValley.tail {N : ℕ} {γ : Fin (N+1) → ℕ} {k : ℕ} (h : IsValley γ k) :
    IsValley (Fin.tail γ) (k-1) := by
  refine ⟨fun i j hij hj => h.1 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) ?_,
    fun i j hij hi => h.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) ?_⟩
  · have := j.isLt; simp only [Fin.val_succ]; omega
  · simp only [Fin.val_succ]; omega

theorem IsValley.init {N : ℕ} {γ : Fin (N+1) → ℕ} {k : ℕ} (h : IsValley γ k) :
    IsValley (Fin.init γ) k :=
  ⟨fun i j hij hj => h.1 i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij) hj,
    fun i j hij hi => h.2 i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij) hi⟩

/-- A valley is bounded by its larger end value. -/
theorem IsValley.le_ends {N : ℕ} {γ : Fin (N+1) → ℕ} {k : ℕ} (h : IsValley γ k) (j : Fin (N+1)) :
    γ j ≤ γ 0 ∨ γ j ≤ γ (Fin.last N) := by
  by_cases hj : j.val < k
  · left
    rcases (Fin.zero_le j).lt_or_eq with h0 | h0
    · exact le_of_lt (h.1 0 j h0 hj)
    · rw [h0]
  · right
    rcases (Fin.le_last j).lt_or_eq with hl | hl
    · exact le_of_lt (h.2 j _ hl (by omega))
    · rw [hl]

theorem armSum_cons {N : ℕ} (γ : Fin (N+1) → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    armSum γ k = armSum (Fin.tail γ) (k-1) := by
  rw [armSum, armSum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.tail]
  rw [if_neg (by omega), zero_add]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases h : k ≤ j.val + 1
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem armSum_snoc {N : ℕ} (γ : Fin (N+1) → ℕ) (k : ℕ) (hk : k ≤ N) :
    armSum γ k = armSum (Fin.init γ) k + (γ (Fin.last N)).choose 3 := by
  rw [armSum, armSum, Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, Fin.init]
  rw [if_pos hk]

/-- Distinct naturals indexed by `Fin m` sum to at least `binom(m,2)`. -/
theorem choose_two_le_sum_of_injective : ∀ {m : ℕ} (γ : Fin m → ℕ), Function.Injective γ →
    m.choose 2 ≤ ∑ j, γ j
  | 0, _, _ => by simp
  | m+1, γ, hγ => by
      obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ γ Finset.univ_nonempty
      have ih : m.choose 2 ≤ ∑ i, γ (j0.succAbove i) :=
        choose_two_le_sum_of_injective (fun i => γ (j0.succAbove i))
          (hγ.comp Fin.succAbove_right_injective)
      rw [Fin.sum_univ_succAbove γ j0]
      have hmax : m ≤ γ j0 := by
        by_contra hlt
        push_neg at hlt
        have hinj : Function.Injective (fun j : Fin (m+1) => (⟨γ j, by
            have := hj0 j (Finset.mem_univ _); omega⟩ : Fin m)) := by
          intro a b h
          exact hγ (by simpa using congrArg Fin.val h)
        have := Fintype.card_le_of_injective _ hinj
        simp at this
      have hc : (m+1).choose 2 = m.choose 2 + m := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      omega

/-- Distinct naturals of minimal total `binom(m,2)` are all `< m`. -/
theorem lt_of_injective_of_sum {m : ℕ} (γ : Fin m → ℕ) (hγ : Function.Injective γ)
    (hs : ∑ j, γ j = m.choose 2) (j : Fin m) : γ j < m := by
  rcases m with _ | m
  · exact j.elim0
  by_contra hge
  push_neg at hge
  have h := choose_two_le_sum_of_injective (fun i => γ (j.succAbove i))
    (hγ.comp Fin.succAbove_right_injective)
  rw [Fin.sum_univ_succAbove γ j] at hs
  have hc : (m+1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
  simp only at h
  omega

theorem snoc_injective_iff {N : ℕ} (p : Fin N → ℕ) (x : ℕ) :
    Function.Injective (Fin.snoc p x : Fin (N+1) → ℕ) ↔
      Function.Injective p ∧ x ∉ Set.range p := by
  constructor
  · intro h
    refine ⟨fun a b hab => Fin.castSucc_injective _ (h (by simpa using hab)), ?_⟩
    rintro ⟨a, ha⟩
    have h2 : (Fin.snoc p x : Fin (N+1) → ℕ) a.castSucc =
        (Fin.snoc p x : Fin (N+1) → ℕ) (Fin.last N) := by
      simp [ha]
    exact (Fin.castSucc_lt_last a).ne (h h2)
  · rintro ⟨hp, hx⟩ a b hab
    induction a using Fin.lastCases with
    | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b => exact absurd ⟨b, by simpa using hab.symm⟩ hx
    | cast a =>
        induction b using Fin.lastCases with
        | last => exact absurd ⟨a, by simpa using hab⟩ hx
        | cast b => exact congrArg _ (hp (by simpa using hab))

/-- Top-degree valley theorem. -/
theorem top_valley : ∀ (N : ℕ) (γ : Fin N → ℕ) (k : ℕ), IsValley γ k →
    ∑ j, γ j = N.choose 2 →
    top N γ = if Function.Injective γ then (-1 : ℤ)^(N.choose 3 + armSum γ k) else 0
  | 0, γ, k, _, _ => by
      have hγ : γ = 0 := Subsingleton.elim _ _
      subst hγ
      have hi : Function.Injective (0 : Fin 0 → ℕ) := fun a => a.elim0
      rw [if_pos hi]
      change (Finsupp.single (0 : Fin 0 → ℕ) (1 : ℤ)) 0 = _
      simp [armSum]
  | 1, γ, k, _, hs => by
      have hγ : γ = 0 := by funext j; fin_cases j; simpa using hs
      subst hγ
      have : Function.Injective (0 : Fin 1 → ℕ) := fun a b _ => Subsingleton.elim a b
      rw [if_pos this]
      change (Finsupp.single (0 : Fin 1 → ℕ) (1 : ℤ)) 0 = _
      simp [armSum, Nat.choose_eq_zero_of_lt]
  | 2, γ, k, _, hs => by
      have h01 : γ 0 + γ 1 = 1 := by simpa [Fin.sum_univ_two] using hs
      have harm : armSum γ k = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        split_ifs
        · exact Nat.choose_eq_zero_of_lt (by fin_cases j <;> simp <;> omega)
        · rfl
      rw [harm, add_zero, show Nat.choose 2 3 = 0 by decide, pow_zero]
      have hinj : Function.Injective γ := by
        intro a b h
        fin_cases a <;> fin_cases b <;> simp_all <;> omega
      rw [if_pos hinj]
      rcases Nat.eq_zero_or_pos (γ 1) with h1 | h1
      · have hγ : γ = fun i => 2-1-i.val := by
          funext j; fin_cases j <;> simp <;> omega
        rw [hγ, top_staircase]
        rfl
      · have hγ : γ = fun i => i.val := by
          funext j; fin_cases j <;> simp <;> omega
        rw [hγ, top_increasing]
        rfl
  | n+3, γ, k, hv, hs => by
      have hc2 : (n+3).choose 2 = (n+2).choose 2 + (n+2) := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      have hc3 : (n+3).choose 3 = (n+2).choose 2 + (n+2).choose 3 := Nat.choose_succ_succ' _ _
      by_cases hsmall : γ 0 ≤ n+1 ∧ γ (Fin.last (n+2)) ≤ n+1
      · -- every exponent is at most `N − 2`
        have hle : ∀ j, γ j ≤ n+1 := fun j => by
          rcases hv.le_ends j with h | h <;> omega
        have hz : top (n+3) γ = 0 := by
          rw [top, StaircaseSorting.D_monomial_eq_zero_of_small (n := n+1) γ hle]; rfl
        have hni : ¬ Function.Injective γ := fun hinj => by
          have hinj' : Function.Injective
              (fun j => (⟨γ j, Nat.lt_succ_of_le (hle j)⟩ : Fin (n+2))) :=
            fun a b h => hinj (by simpa using congrArg Fin.val h)
          have := Fintype.card_le_of_injective _ hinj'
          simp at this
        rw [hz, if_neg hni]
      rcases le_total (γ (Fin.last (n+2))) (γ 0) with hlr | hrl
      · -- the maximum is the first exponent
        have h0 : n+2 ≤ γ 0 := by omega
        have hk : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · have := hv.2 0 (Fin.last (n+2)) (by simp [Fin.lt_def]) (by rw [hk0]; exact Nat.zero_le _)
            omega
          · exact hk0
        have hsum : γ 0 + ∑ j, Fin.tail γ j = (n+3).choose 2 := by
          rw [← hs, Fin.sum_univ_succ γ]; rfl
        rcases h0.lt_or_eq with hgt | heq
        · have hlow : ∑ j, Fin.tail γ j < (n+2).choose 2 := by omega
          have hz : top (n+3) γ = 0 := by
            rw [top, ← Fin.cons_self_tail γ, left_peel_low n _ _ hlow]; rfl
          have hni : ¬ Function.Injective γ := fun hinj => by
            have := choose_two_le_sum_of_injective (Fin.tail γ) (hinj.comp (Fin.succ_injective _))
            omega
          rw [hz, if_neg hni]
        · have hs2 : ∑ j, Fin.tail γ j = (n+2).choose 2 := by omega
          have hcons : (Fin.cons (n+2) (Fin.tail γ) : Fin (n+3) → ℕ) = γ := by
            funext j
            refine Fin.cases ?_ (fun j => ?_) j
            · simp [heq]
            · simp [Fin.tail]
          have hpeel := left_peel n (Fin.tail γ) hs2
          rw [hcons, top_valley (n+2) (Fin.tail γ) (k-1) hv.tail hs2] at hpeel
          have hiff : Function.Injective γ ↔ Function.Injective (Fin.tail γ) := by
            constructor
            · intro h; exact h.comp (Fin.succ_injective _)
            · intro h
              rw [← hcons, Fin.cons_injective_iff]
              refine ⟨?_, h⟩
              rintro ⟨j, hj⟩
              have := lt_of_injective_of_sum _ h hs2 j
              omega
          rw [hpeel]
          by_cases hi : Function.Injective (Fin.tail γ)
          · rw [if_pos hi, if_pos (hiff.mpr hi), armSum_cons γ k hk, ← pow_add, hc3]
            congr 1
            ring
          · rw [if_neg hi, if_neg (fun h => hi (hiff.mp h)), mul_zero]
      · -- the maximum is the last exponent
        have hl : n+2 ≤ γ (Fin.last (n+2)) := by omega
        have hk : k ≤ n+2 := by
          rcases Nat.lt_or_ge (n+2) k with hk0 | hk0
          · have := hv.1 0 (Fin.last (n+2)) (by simp [Fin.lt_def]) (by simp; omega)
            omega
          · exact hk0
        have hsum : ∑ j, Fin.init γ j + γ (Fin.last (n+2)) = (n+3).choose 2 := by
          rw [← hs, Fin.sum_univ_castSucc γ]; rfl
        rcases hl.lt_or_eq with hgt | heq
        · have hlow : ∑ j, Fin.init γ j < (n+2).choose 2 := by omega
          have hz : top (n+3) γ = 0 := by
            rw [top, ← Fin.snoc_init_self γ, right_peel_low n _ _ hlow]; rfl
          have hni : ¬ Function.Injective γ := fun hinj => by
            have := choose_two_le_sum_of_injective (Fin.init γ)
              (hinj.comp (Fin.castSucc_injective _))
            omega
          rw [hz, if_neg hni]
        · have hs2 : ∑ j, Fin.init γ j = (n+2).choose 2 := by omega
          have hsnoc : (Fin.snoc (Fin.init γ) (n+2) : Fin (n+3) → ℕ) = γ := by
            funext j
            refine Fin.lastCases ?_ (fun j => ?_) j
            · simp [heq]
            · simp [Fin.init]
          have hpeel := right_peel n (Fin.init γ) hs2
          rw [hsnoc, top_valley (n+2) (Fin.init γ) k hv.init hs2] at hpeel
          have hiff : Function.Injective γ ↔ Function.Injective (Fin.init γ) := by
            constructor
            · intro h; exact h.comp (Fin.castSucc_injective _)
            · intro h
              have hx : (n+2) ∉ Set.range (Fin.init γ) := by
                rintro ⟨j, hj⟩
                have := lt_of_injective_of_sum _ h hs2 j
                omega
              have := (snoc_injective_iff (Fin.init γ) (n+2)).mpr ⟨h, hx⟩
              rwa [hsnoc] at this
          rw [hpeel]
          by_cases hi : Function.Injective (Fin.init γ)
          · rw [if_pos hi, if_pos (hiff.mpr hi), armSum_snoc γ k hk, ← heq, ← pow_add]
            congr 1
            ring
          · rw [if_neg hi, if_neg (fun h => hi (hiff.mp h)), mul_zero]
end OddMath.Frontier.StaircaseValley

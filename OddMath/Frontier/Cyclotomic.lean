import OddMath.Frontier.NilHeckeEndomorphism
import OddMath.Frontier.MonomialReversal
import OddMath.Frontier.ElementaryGeneration

/-! # Odd Grassmannian rings and cyclotomic quotients
EKL arXiv:1111.1320v1 §5, pp.44–46. Rank is a = n+2. Both quotients are by two-sided ideals
of noncommutative rings.

* p.44: `OH n N = OΛ_a/⟨h_m : m > N − a⟩`, `ONH n N = ONH_a/⟨x̃_1^N⟩`; `OH_{a,N} = 0` for
  `a > N`, `OH_{a,a} ≅ ℤ`.
* (5.5)–(5.7), p.45: coefficientwise in the super-central variable `t`.
* Lemma 5.1, (5.4), pp.44–45: the printed display `x̃_1^a y = Σ_j (-1)^{C(j-1,2)} ε_j x̃_1^{a-j} y`
  holds (LEFT coefficients). In the RIGHT `OΛ_a`-coordinates of Corollary 2.14, where `φ(x̃_1)`
  is linear, the first column is `(-1)^{j(|β|+1)+1} ε_j`; the printed matrix is refuted there.
* (5.8), (5.9), p.45–46: refuted as printed; corrected forms of the relevant cases.
Proposition 5.2 is in `CyclotomicMatrix`. -/
namespace OddMath.Frontier.Cyclotomic
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle sum_expSingle)
open FiniteCompleteElementary FiniteCompleteElementary.FiniteWords PlacticEvaluation
open OddSymmetricKernel NilHeckeAction
open scoped BigOperators
noncomputable section

/-- `OΛ_a`, the joint kernel, as a ring. -/
abbrev K (n : ℕ) := kernelSubring n

/-- The odd complete polynomial `h_m ∈ OΛ_a` (EKL (2.30), p.44). -/
def hK (n m : ℕ) : K n := ⟨completePoly (n+2) m, complete_mem n m⟩

/-- The odd elementary polynomial `ε_m ∈ OΛ_a` (EKL (5.2)). -/
def eK (n m : ℕ) : K n := ⟨elementaryPoly (n+2) m, elementary_mem n m⟩

@[simp] theorem hK_val (n m : ℕ) : (hK n m : SkewPolynomial (n+2)) = completePoly (n+2) m := rfl
@[simp] theorem eK_val (n m : ℕ) : (eK n m : SkewPolynomial (n+2)) = elementaryPoly (n+2) m := rfl

@[simp] theorem hK_zero (n : ℕ) : hK n 0 = 1 := Subtype.ext (completePoly_zero _)
@[simp] theorem eK_zero (n : ℕ) : eK n 0 = 1 := Subtype.ext (elementaryPoly_zero _)

/-- The generators `h_m`, `m > N − a`, written without truncated subtraction. -/
def grassmannianGenerators (n N : ℕ) : Set (K n) := {x | ∃ m, N < m + (n+2) ∧ hK n m = x}

/-- `⟨h_m : m > N − a⟩ ⊂ OΛ_a`, EKL p.44. -/
def grassmannianIdeal (n N : ℕ) : TwoSidedIdeal (K n) :=
  TwoSidedIdeal.span (grassmannianGenerators n N)

/-- The odd Grassmannian ring `OH_{a,N} = OΛ_a/⟨h_m : m > N − a⟩`, EKL p.44, a = n+2. -/
def OH (n N : ℕ) : Type := K n ⧸ (grassmannianIdeal n N).asIdeal

instance (n N : ℕ) : Ring (OH n N) := Ideal.Quotient.ring _

/-- The quotient map `OΛ_a → OH_{a,N}`. -/
def toOH (n N : ℕ) : K n →+* OH n N := Ideal.Quotient.mk _

theorem toOH_surjective (n N : ℕ) : Function.Surjective (toOH n N) :=
  Ideal.Quotient.mk_surjective

theorem toOH_eq_zero_iff (n N : ℕ) (x : K n) : toOH n N x = 0 ↔ x ∈ grassmannianIdeal n N :=
  Ideal.Quotient.eq_zero_iff_mem.trans TwoSidedIdeal.mem_asIdeal

theorem hK_mem (n N m : ℕ) (hm : N < m + (n+2)) : hK n m ∈ grassmannianIdeal n N :=
  TwoSidedIdeal.subset_span ⟨m, hm, rfl⟩

@[simp] theorem toOH_hK (n N m : ℕ) (hm : N < m + (n+2)) : toOH n N (hK n m) = 0 :=
  (toOH_eq_zero_iff n N _).mpr (hK_mem n N m hm)

/-- The dot on the first strand. EKL p.5: `x̃_1 = x_1` (the tilde sign is `(-1)^{i-1}`). -/
def firstDot (n : ℕ) : Presented n := dot n 0

/-- `⟨x̃_1^N⟩ ⊂ ONH_a`, EKL p.44. -/
def cyclotomicIdeal (n N : ℕ) : TwoSidedIdeal (Presented n) :=
  TwoSidedIdeal.span {firstDot n ^ N}

/-- The cyclotomic quotient `ONH_a^N = ONH_a/⟨x̃_1^N⟩`, EKL p.44, a = n+2. -/
def ONH (n N : ℕ) : Type := Presented n ⧸ (cyclotomicIdeal n N).asIdeal

instance (n N : ℕ) : Ring (ONH n N) := Ideal.Quotient.ring _

/-- The quotient map `ONH_a → ONH_a^N`. -/
def toONH (n N : ℕ) : Presented n →+* ONH n N := Ideal.Quotient.mk _

theorem toONH_surjective (n N : ℕ) : Function.Surjective (toONH n N) :=
  Ideal.Quotient.mk_surjective

theorem toONH_eq_zero_iff (n N : ℕ) (x : Presented n) :
    toONH n N x = 0 ↔ x ∈ cyclotomicIdeal n N :=
  Ideal.Quotient.eq_zero_iff_mem.trans TwoSidedIdeal.mem_asIdeal

@[simp] theorem toONH_firstDot_pow (n N : ℕ) : toONH n N (firstDot n ^ N) = 0 :=
  (toONH_eq_zero_iff n N _).mpr (TwoSidedIdeal.subset_span rfl)

/-- EKL p.44: `OH_{a,N}` vanishes unless `a ≤ N` (`h_0 = 1` is a generator). -/
theorem OH_subsingleton {n N : ℕ} (h : N < n+2) : Subsingleton (OH n N) := by
  have h1 : toOH n N 1 = 0 := by rw [← hK_zero]; exact toOH_hK n N 0 (by omega)
  rw [map_one] at h1
  exact subsingleton_of_zero_eq_one h1.symm

/-! ### (5.5)–(5.7): the alternate presentation, coefficientwise in `t` -/

theorem choose_two_add (k l : ℕ) :
    (k+l+1).choose 2 = (k+1).choose 2 + (l+1).choose 2 + k*l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show k + (l+1) + 1 = (k+l+1) + 1 by omega, Nat.choose_succ_succ', ih,
      Nat.choose_succ_succ' (l+1), Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem neg_one_pow_add_two_mul (x y : ℕ) : (-1 : ℤ)^(x + 2*y) = (-1)^x := by
  rw [pow_add, pow_mul]; simp

/-- The super-central sign: `ε_k t^k z_l t^l = (-1)^{kl} ε_k z_l t^{k+l}`. -/
theorem sign_identity (k l : ℕ) :
    (-1 : ℤ)^(k*l) * (-1)^((l+1).choose 2) = (-1)^((k+l+1).choose 2) * (-1)^((k+1).choose 2) := by
  rw [← pow_add, ← pow_add, choose_two_add]
  rw [show (k+1).choose 2 + (l+1).choose 2 + k*l + (k+1).choose 2 =
    (k*l + (l+1).choose 2) + 2*((k+1).choose 2) by ring, neg_one_pow_add_two_mul]

/-- `z_k = (-1)^{C(k+1,2)} h_k`, EKL (5.7). -/
def zK (n k : ℕ) : K n := (-1 : ℤ)^((k+1).choose 2) • hK n k

@[simp] theorem zK_zero (n : ℕ) : zK n 0 = 1 := by simp [zK]

theorem eK_eq_zero {n k : ℕ} (hk : n+2 < k) : eK n k = 0 :=
  Subtype.ext (elementaryPoly_eq_zero_of_lt hk)

/-- EKL (5.5), coefficient of `t^m` (`m ≥ 1`), with `t` super-central:
`Σ_k (-1)^{k(m-k)} ε_k z_{m-k} = 0`. -/
theorem supercentral_inverse (n m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range (m+1), (-1 : ℤ)^(k*(m-k)) • (eK n k * zK n (m-k)) = 0 := by
  apply Subtype.ext
  have h := elementary_complete_inverse (n+2) m hm
  have h2 := congrArg (fun p => (-1 : ℤ)^((m+1).choose 2) • p) h
  simp only [smul_zero, Finset.smul_sum, smul_smul] at h2
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Subring.coe_mul, eK_val, zK,
    hK_val, ZeroMemClass.coe_zero, mul_smul_comm, smul_smul]
  rw [← h2]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [Nat.add_sub_cancel_left, sign_identity]
  rfl

/-- EKL (5.5), converse: `z_k` is the unique solution with `z_0 = 1`. -/
theorem supercentral_inverse_unique (n : ℕ) (z : ℕ → K n) (h0 : z 0 = 1)
    (hz : ∀ m, 0 < m →
      ∑ k ∈ Finset.range (m+1), (-1 : ℤ)^(k*(m-k)) • (eK n k * z (m-k)) = 0) :
    z = zK n := by
  funext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [h0, zK_zero]
    have h1 := hz m hm
    have h2 := supercentral_inverse n m hm
    rw [Finset.sum_range_succ'] at h1 h2
    have hs : ∑ k ∈ Finset.range m, (-1 : ℤ)^((k+1)*(m-(k+1))) • (eK n (k+1) * z (m-(k+1))) =
        ∑ k ∈ Finset.range m, (-1 : ℤ)^((k+1)*(m-(k+1))) • (eK n (k+1) * zK n (m-(k+1))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih (m-(k+1)) (by have := Finset.mem_range.mp hk; omega)]
    simp only [Nat.zero_mul, pow_zero, one_smul, eK_zero, one_mul, Nat.sub_zero] at h1 h2
    rw [hs] at h1
    exact add_left_cancel (h1.trans h2.symm)

/-- The coefficient of `t^m` in the truncated product (5.6)
`(1 + ε_1 t + ⋯ + ε_a t^a)(1 + z_1 t + ⋯ + z_{N-a} t^{N-a})`, with `t` super-central. -/
def grassmannRelation (n N m : ℕ) : K n :=
  ∑ k ∈ Finset.range (m+1),
    if k ≤ n+2 ∧ m - k ≤ N - (n+2) then (-1 : ℤ)^(k*(m-k)) • (eK n k * zK n (m-k)) else 0

theorem zK_mem (n N m : ℕ) (hm : N < m + (n+2)) : zK n m ∈ grassmannianIdeal n N :=
  TwoSidedIdeal.zsmul_mem _ _ (hK_mem n N m hm)

/-- Splitting (5.5) along the truncation of (5.6). -/
theorem grassmannRelation_eq (n N m : ℕ) (hm : 0 < m) :
    grassmannRelation n N m = -∑ k ∈ Finset.range (m+1),
      if k ≤ n+2 ∧ m - k ≤ N - (n+2) then 0 else (-1 : ℤ)^(k*(m-k)) • (eK n k * zK n (m-k)) := by
  rw [eq_neg_iff_add_eq_zero, grassmannRelation, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl ?_).trans (supercentral_inverse n m hm)
  intro k _
  split_ifs <;> simp

theorem grassmannRelation_mem (n N m : ℕ) (hN : n+2 ≤ N) (hm : 0 < m) :
    grassmannRelation n N m ∈ grassmannianIdeal n N := by
  rw [grassmannRelation_eq n N m hm]
  apply TwoSidedIdeal.neg_mem
  refine sum_mem (fun k hk => ?_)
  split_ifs with h
  · exact TwoSidedIdeal.zero_mem _
  · rw [not_and_or] at h
    rcases h with h | h
    · rw [eK_eq_zero (by omega), zero_mul, smul_zero]; exact TwoSidedIdeal.zero_mem _
    · exact TwoSidedIdeal.zsmul_mem _ _ (TwoSidedIdeal.mul_mem_left _ _ _ (zK_mem n N _ (by omega)))

/-- The relations of (5.6), all powers `t^m` with `m ≥ 1`. -/
def grassmannRelations (n N : ℕ) : Set (K n) := {x | ∃ m, 0 < m ∧ grassmannRelation n N m = x}

/-- EKL (5.6)–(5.7): the coefficients of (5.6) generate `⟨h_m : m > N − a⟩`, for `a ≤ N`. -/
theorem span_grassmannRelations (n N : ℕ) (hN : n+2 ≤ N) :
    TwoSidedIdeal.span (grassmannRelations n N) = grassmannianIdeal n N := by
  apply le_antisymm
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact grassmannRelation_mem n N m hN hm
  · rw [grassmannianIdeal, TwoSidedIdeal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    set J := TwoSidedIdeal.span (grassmannRelations n N)
    suffices hz : ∀ m, N < m + (n+2) → zK n m ∈ J by
      have h := TwoSidedIdeal.zsmul_mem J ((-1 : ℤ)^((m+1).choose 2)) (hz m hm)
      rwa [zK, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul] at h
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hm0 : 0 < m := by omega
      have hR : grassmannRelation n N m ∈ J := TwoSidedIdeal.subset_span ⟨m, hm0, rfl⟩
      rw [grassmannRelation_eq n N m hm0, Finset.sum_range_succ'] at hR
      have hc : ¬ (0 ≤ n+2 ∧ m - 0 ≤ N - (n+2)) := by omega
      simp only [hc, if_false, Nat.zero_mul, pow_zero, one_smul, eK_zero, one_mul,
        Nat.sub_zero] at hR
      have hrest : (∑ k ∈ Finset.range m, if k+1 ≤ n+2 ∧ m - (k+1) ≤ N - (n+2) then 0 else
          (-1 : ℤ)^((k+1)*(m-(k+1))) • (eK n (k+1) * zK n (m-(k+1)))) ∈ J := by
        refine sum_mem (fun k hk => ?_)
        have hk' := Finset.mem_range.mp hk
        split_ifs with h
        · exact TwoSidedIdeal.zero_mem _
        · rw [not_and_or] at h
          rcases h with h | h
          · rw [eK_eq_zero (by omega), zero_mul, smul_zero]; exact TwoSidedIdeal.zero_mem _
          · exact TwoSidedIdeal.zsmul_mem _ _
              (TwoSidedIdeal.mul_mem_left _ _ _ (ih _ (by omega) (by omega)))
      have hmN : ¬ m ≤ N - (n+2) := by omega
      have := TwoSidedIdeal.sub_mem J (TwoSidedIdeal.neg_mem J hR) hrest
      simpa [hmN] using this

/-! ### Lemma 5.1: the action of `x̃_1` on `span B_β` (EKL pp.44–45) -/

section Words
variable {R : Type*} [Ring R]

theorem strictSum_eq_zero_of_lt {m k : ℕ} (x : Fin m → R) (h : m < k) : strictSum x k = 0 := by
  classical
  rw [strictSum_eq]
  apply Finset.sum_eq_zero
  intro f _
  have hf : ¬ StrictMono f := by
    intro hf
    have hc := Fintype.card_le_of_injective f hf.injective
    simp only [Fintype.card_fin] at hc
    omega
  simp only [hf, ↓reduceIte]

/-- Right-coefficient telescoping behind Lemma 5.1: for `y` with `x₀ y = (-1)^d y x₀`,
`Σ_{j≤k} (-1)^{j(d+1)} x₀^{k-j} y e_j(x) = (-1)^{k(d+1)} y e_k(x₁,…)`. -/
theorem right_telescope {m : ℕ} (x : Fin (m+1) → R) (y : R) (d : ℕ)
    (hy : x 0 * y = (-1 : ℤ)^d • (y * x 0)) (k : ℕ) :
    ∑ j ∈ Finset.range (k+1), (-1 : ℤ)^(j*(d+1)) • (x 0^(k-j) * y * strictSum x j) =
      (-1 : ℤ)^(k*(d+1)) • (y * strictSum (fun i => x i.succ) k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    have hs : ∑ j ∈ Finset.range (k+1), (-1 : ℤ)^(j*(d+1)) • (x 0^(k+1-j) * y * strictSum x j) =
        x 0 * ∑ j ∈ Finset.range (k+1), (-1 : ℤ)^(j*(d+1)) • (x 0^(k-j) * y * strictSum x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : k + 1 - j = (k - j) + 1 := by have := Finset.mem_range.mp hj; omega
      rw [hjk, pow_succ', mul_smul_comm, mul_assoc, mul_assoc, mul_assoc]
    have ht : (-1 : ℤ)^((k+1)*(d+1)) = -((-1)^(k*(d+1)) * (-1)^d) := by
      rw [add_mul, one_mul, pow_add, pow_succ, ← mul_assoc]; ring
    rw [hs, ih, mul_smul_comm, ← mul_assoc, hy, strictSum_succ, ht]
    simp only [smul_mul_assoc, mul_add, smul_add, smul_smul, mul_assoc, neg_smul]
    abel

/-- Left-coefficient telescoping behind the display in the proof of Lemma 5.1:
`Σ_{j≤k} (-1)^{C(j+1,2)} e_j(x) x₀^{k-j} = (-1)^{C(k+1,2)} e_k(x₁,…)`. -/
theorem left_telescope {m : ℕ} (x : Fin (m+1) → R)
    (ha : ∀ i : Fin m, x 0 * x i.succ = -(x i.succ * x 0)) (k : ℕ) :
    ∑ j ∈ Finset.range (k+1), (-1 : ℤ)^((j+1).choose 2) • (strictSum x j * x 0^(k-j)) =
      (-1 : ℤ)^((k+1).choose 2) • strictSum (fun i => x i.succ) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ j ∈ Finset.range (k+1), (-1 : ℤ)^((j+1).choose 2) • (strictSum x j * x 0^(k+1-j)) =
        (∑ j ∈ Finset.range (k+1), (-1 : ℤ)^((j+1).choose 2) • (strictSum x j * x 0^(k-j))) * x 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : k + 1 - j = (k - j) + 1 := by have := Finset.mem_range.mp hj; omega
      rw [hjk, pow_succ, smul_mul_assoc, mul_assoc]
    have ht : (-1 : ℤ)^((k+2).choose 2) * (-1)^k = -((-1) ^ ((k+1).choose 2)) := sign_step k
    rw [hs, ih, strictSum_succ, mul_strictSum (x 0) (fun i => x i.succ) ha]
    simp only [smul_mul_assoc, smul_add, smul_smul, show k + 1 + 1 = k + 2 from rfl, ht, neg_smul]
    abel

end Words


/-- `x̃_1 = x_1` as an element of `OPol_a`. -/
abbrev x1 (n : ℕ) : SkewPolynomial (n+2) := generator 0

theorem tilde_zero (n : ℕ) : tildeGenerator (0 : Fin (n+2)) = x1 n := by
  simp [tildeGenerator]

theorem tilde_first_anticommute (n : ℕ) (i : Fin (n+1)) :
    tildeGenerator (n := n+2) 0 * tildeGenerator i.succ =
      -(tildeGenerator i.succ * tildeGenerator 0) :=
  tilde_anticommute _ _ (Fin.succ_ne_zero i).symm

theorem choose_two_add_two (j : ℕ) : (j+2).choose 2 = j.choose 2 + 2*j + 1 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.choose_succ_succ', Nat.choose_one_right]
  ring

/-- The display closing the proof of Lemma 5.1, with its `Σ_{j=1}^n` read as `Σ_{j=1}^a`:
`x̃_1^a y = Σ_{j=1}^a (-1)^{C(j-1,2)} ε_j x̃_1^{a-j} y` (LEFT coefficients), for every `y`. -/
theorem lemma_5_1_left (n : ℕ) (y : SkewPolynomial (n+2)) :
    x1 n ^ (n+2) * y = ∑ j ∈ Finset.range (n+2),
      (-1 : ℤ)^(j.choose 2) • (elementaryPoly (n+2) (j+1) * x1 n ^ (n+1-j) * y) := by
  have h := left_telescope (tildeGenerator (n := n+2)) (tilde_first_anticommute n) (n+2)
  rw [strictSum_eq_zero_of_lt _ (by omega), smul_zero, Finset.sum_range_succ'] at h
  simp only [strictSum_zero, tilde_zero, Nat.sub_zero, one_mul, zero_add,
    ← elementaryPoly_eq_strictSum] at h
  rw [show (Nat.choose 1 2) = 0 from rfl, pow_zero, one_smul] at h
  rw [eq_neg_of_add_eq_zero_right h, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_mul_assoc, ← neg_smul, show n + 2 - (j+1) = n+1-j by omega, choose_two_add_two,
    pow_succ, pow_add, pow_mul]
  simp

/-- Right-coefficient form of Lemma 5.1: if `x̃_1 y = (-1)^d y x̃_1` then
`x̃_1^a y = Σ_{j=1}^a x̃_1^{a-j} y · (-1)^{j(d+1)+1} ε_j`. -/
theorem lemma_5_1_right (n d : ℕ) (y : SkewPolynomial (n+2))
    (hy : x1 n * y = (-1 : ℤ)^d • (y * x1 n)) :
    x1 n ^ (n+2) * y = ∑ j ∈ Finset.range (n+2),
      x1 n ^ (n+1-j) * y * ((-1 : ℤ)^((j+1)*(d+1)+1) • elementaryPoly (n+2) (j+1)) := by
  rw [← tilde_zero] at hy
  have h := right_telescope (tildeGenerator (n := n+2)) y d hy (n+2)
  rw [strictSum_eq_zero_of_lt _ (by omega), mul_zero, smul_zero, Finset.sum_range_succ'] at h
  simp only [strictSum_zero, tilde_zero, Nat.sub_zero, mul_one, Nat.zero_mul, pow_zero, one_smul,
    ← elementaryPoly_eq_strictSum] at h
  rw [eq_neg_of_add_eq_zero_right h, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_smul_comm, show n + 2 - (j+1) = n+1-j by omega, pow_succ, ← neg_smul, mul_neg_one]

/-- The family `B_β = (x̃_1^{a-1} y, …, x̃_1 y, y)` of EKL p.44 (`y = x̃^β`). -/
def basisB (n : ℕ) (y : SkewPolynomial (n+2)) (i : Fin (n+2)) : SkewPolynomial (n+2) :=
  x1 n ^ (n+1-i.val) * y

/-- The true matrix of `φ(x̃_1)` on `B_β` in RIGHT `OΛ_a`-coordinates (the convention of
Corollary 2.14): first column `((-1)^{j(d+1)+1} ε_j)_{j=1..a}` with `d = |β|`, and ones on the
superdiagonal. -/
def rightMatrix (n d : ℕ) : Matrix (Fin (n+2)) (Fin (n+2)) (K n) := fun i k =>
  if k.val = 0 then (-1 : ℤ)^((i.val+1)*(d+1)+1) • eK n (i.val+1)
  else if i.val + 1 = k.val then 1 else 0

/-- The matrix (5.4) as printed: first column `((-1)^{C(j-1,2)} ε_j)_{j=1..a}`. -/
def printedMatrix (n : ℕ) : Matrix (Fin (n+2)) (Fin (n+2)) (K n) := fun i k =>
  if k.val = 0 then (-1 : ℤ)^(i.val.choose 2) • eK n (i.val+1)
  else if i.val + 1 = k.val then 1 else 0

/-- Lemma 5.1, corrected, column form: `x̃_1 · B_k = Σ_i B_i · M_{ik}` with right coefficients,
whenever `x̃_1 y = (-1)^d y x̃_1` (e.g. `y = x̃^β`, `β_1 = 0`, `|β| = d`). -/
theorem lemma_5_1 (n d : ℕ) (y : SkewPolynomial (n+2))
    (hy : x1 n * y = (-1 : ℤ)^d • (y * x1 n)) (k : Fin (n+2)) :
    x1 n * basisB n y k = ∑ i, basisB n y i * (rightMatrix n d i k : SkewPolynomial (n+2)) := by
  by_cases hk : k.val = 0
  · simp only [basisB, rightMatrix, hk, if_true, Nat.sub_zero]
    rw [← mul_assoc, ← pow_succ', lemma_5_1_right n d y hy,
      ← Fin.sum_univ_eq_sum_range (fun j => x1 n ^ (n+1-j) * y *
        ((-1 : ℤ)^((j+1)*(d+1)+1) • elementaryPoly (n+2) (j+1)))]
    rfl
  · have hk1 : k.val - 1 < n+2 := by omega
    rw [Finset.sum_eq_single ⟨k.val - 1, hk1⟩]
    · simp only [basisB, rightMatrix, hk, if_false, show k.val - 1 + 1 = k.val by omega, if_true,
        OneMemClass.coe_one, mul_one]
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    · intro i _ hi
      have : ¬ i.val + 1 = k.val := fun h => hi (Fin.ext (by simp; omega))
      simp [rightMatrix, hk, this]
    · simp

/-- Lemma 5.1, corrected, as a statement about the right `OΛ_a`-span of `B_β`. -/
theorem lemma_5_1_span (n d : ℕ) (y : SkewPolynomial (n+2))
    (hy : x1 n * y = (-1 : ℤ)^d • (y * x1 n)) (c : Fin (n+2) → K n) :
    x1 n * ∑ k, basisB n y k * (c k : SkewPolynomial (n+2)) =
      ∑ i, basisB n y i * ((∑ k, rightMatrix n d i k * c k : K n) : SkewPolynomial (n+2)) := by
  simp only [Finset.mul_sum, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, lemma_5_1 n d y hy k, Finset.sum_mul]
  simp only [mul_assoc]

theorem elementaryPoly_two_two :
    elementaryPoly 2 2 = -(generator (0 : Fin 2) * generator 1) := by
  rw [elementaryPoly_eq_strictSum, strictSum_succ, strictSum_succ, strictSum_succ]
  simp [tildeGenerator]

/-- Erratum for (5.4): in the right-coordinate convention of Corollary 2.14 the printed matrix
is not the matrix of `φ(x̃_1)` on `B_β`. Counterexample: `a = 2`, `β = 0`; the printed first
column says `x_1^2 = x_1 ε_1 + ε_2`, while `x_1^2 = x_1 ε_1 − ε_2` and `ε_2 = −x_1 x_2 ≠ 0`. -/
theorem lemma_5_1_printed_false :
    x1 0 * basisB 0 1 0 ≠ ∑ i, basisB 0 1 i * (printedMatrix 0 i 0 : SkewPolynomial 2) := by
  intro h
  have ht := lemma_5_1 0 0 1 (by simp) 0
  rw [ht, Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [basisB, rightMatrix, printedMatrix, if_true, Fin.val_zero, Fin.val_one,
    SetLike.val_smul, eK_val] at h
  norm_num at h
  have e2 : elementaryPoly (0+2) 2 = -(generator (0 : Fin 2) * generator 1) :=
    elementaryPoly_two_two
  rw [e2] at h
  have hc := congrArg (fun p : SkewPolynomial 2 => p ![1, 1]) h
  simp only [Finsupp.neg_apply] at hc
  have h11 : (generator (0 : Fin 2) * generator 1 : SkewPolynomial 2) ![1, 1] = 1 :=
    OddMath.SkewPolynomial.ordered_rank_two_coordinate
  rw [h11] at hc
  norm_num at hc

theorem crossingCount_first_left {n : ℕ} (β : Fin (n+2) → ℕ) :
    OddMath.crossingCount (expSingle (0 : Fin (n+2))) β = 0 := by
  unfold OddMath.crossingCount
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_filter] at hj
  have : i ≠ 0 := fun h => by subst h; exact absurd hj.2 (Fin.not_lt_zero j)
  simp [expSingle, Ne.symm this]

theorem crossingCount_first_right {n : ℕ} (β : Fin (n+2) → ℕ) (hβ : β 0 = 0) :
    OddMath.crossingCount β (expSingle (0 : Fin (n+2))) = ∑ i, β i := by
  unfold OddMath.crossingCount
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, sum_expSingle]
  by_cases hi : i = 0
  · subst hi; simp [hβ]
  · have : (0 : Fin (n+2)) < i := Fin.pos_iff_ne_zero.mpr hi
    simp [this]

/-- `x̃_1 x̃^β = (-1)^{|β|} x̃^β x̃_1` when `β_1 = 0`: the hypothesis of `lemma_5_1` for `y = x^β`. -/
theorem first_mul_monomial {n : ℕ} (β : Fin (n+2) → ℕ) (hβ : β 0 = 0) :
    generator (0 : Fin (n+2)) * monomial β 1 = (-1 : ℤ)^(∑ i, β i) • (monomial β 1 * generator 0) := by
  have h1 : generator (0 : Fin (n+2)) * monomial β 1 =
      monomial (expSingle 0 + β) (OddMath.skewSign (expSingle 0) β) := by
    rw [generator, OddMath.Frontier.MonomialReversal.monomial_mul_monomial]; simp
  have h2 : monomial β 1 * generator (0 : Fin (n+2)) =
      monomial (β + expSingle 0) (OddMath.skewSign β (expSingle 0)) := by
    rw [generator, OddMath.Frontier.MonomialReversal.monomial_mul_monomial]; simp
  rw [h1, h2, add_comm (expSingle 0) β, OddMath.skewSign, OddMath.skewSign, crossingCount_first_left,
    crossingCount_first_right β hβ, Finsupp.smul_single, smul_eq_mul, ← pow_add, ← two_mul,
    pow_mul]
  simp

/-- Lemma 5.1, corrected, for `y = x^β` with `β_1 = 0`: the sign depends on the parity of `|β|`. -/
theorem lemma_5_1_monomial (n : ℕ) (β : Fin (n+2) → ℕ) (hβ : β 0 = 0) (k : Fin (n+2)) :
    x1 n * basisB n (monomial β 1) k =
      ∑ i, basisB n (monomial β 1) i *
        (rightMatrix n (∑ i, β i) i k : SkewPolynomial (n+2)) :=
  lemma_5_1 n _ _ (first_mul_monomial β hβ) k

/-! ### `OH_{a,a} ≅ ℤ` (EKL p.44) -/

/-- The constant coefficient of a skew polynomial, as a ring homomorphism. -/
def constTerm (N : ℕ) : SkewPolynomial N →+* ℤ where
  toFun f := f 0
  map_one' := Finsupp.single_eq_same
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => rw [add_mul, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply, add_mul]
    | single a r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ h₁ h₂ => rw [mul_add, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply, mul_add]
      | single b s =>
        change (monomial a r * monomial b s) 0 = (monomial a r) 0 * (monomial b s) 0
        rw [MonomialReversal.monomial_mul_monomial]
        simp only [monomial, Finsupp.single_apply]
        by_cases ha : a = 0
        · by_cases hb : b = 0
          · subst ha hb
            simp [OddMath.SkewPolynomial.skewSign_zero_left]
          · have : a + b ≠ 0 := by
              intro h; apply hb; funext i; have := congrFun h i
              simp only [Pi.add_apply, Pi.zero_apply] at this; show b i = 0; omega
            simp [this, hb, Ne.symm]
        · have : a + b ≠ 0 := by
            intro h; apply ha; funext i; have := congrFun h i
            simp only [Pi.add_apply, Pi.zero_apply] at this; show a i = 0; omega
          simp [this, ha, Ne.symm]

@[simp] theorem constTerm_generator {N : ℕ} (i : Fin N) : constTerm N (generator i) = 0 := by
  change (monomial _ 1 : SkewPolynomial N) 0 = 0
  rw [monomial, Finsupp.single_apply, if_neg]
  intro h
  have := congrFun h i
  simp [OddMath.SkewPolynomial.expSingle] at this

theorem constTerm_word {N m : ℕ} (f : Fin (m+1) → Fin N) :
    constTerm N (List.ofFn (fun i => tildeGenerator (f i))).prod = 0 := by
  rw [List.ofFn_succ, List.prod_cons, map_mul, tildeGenerator, map_zsmul, constTerm_generator,
    smul_zero, zero_mul]

theorem constTerm_completePoly (N m : ℕ) : constTerm N (completePoly N (m+1)) = 0 := by
  rw [completePoly, map_sum]
  apply Finset.sum_eq_zero
  intro f _
  split_ifs
  · exact constTerm_word f
  · exact map_zero _

theorem constTerm_elementaryPoly (N m : ℕ) : constTerm N (elementaryPoly N (m+1)) = 0 := by
  rw [elementaryPoly, map_sum]
  apply Finset.sum_eq_zero
  intro f _
  split_ifs
  · exact constTerm_word f
  · exact map_zero _

/-- For `a = N`, every `ε_k` with `k ≥ 1` lies in `⟨h_m : m ≥ 1⟩`. -/
theorem eK_mem_top (n k : ℕ) : eK n (k+1) ∈ grassmannianIdeal n (n+2) := by
  have h := supercentral_inverse n (k+1) (by omega)
  rw [Finset.sum_range_succ, Nat.sub_self, Nat.mul_zero, pow_zero, one_smul, zK_zero,
    mul_one] at h
  rw [eq_neg_of_add_eq_zero_right h]
  refine TwoSidedIdeal.neg_mem _ (sum_mem fun j hj => ?_)
  have := Finset.mem_range.mp hj
  exact TwoSidedIdeal.zsmul_mem _ _ (TwoSidedIdeal.mul_mem_left _ _ _ (zK_mem n _ _ (by omega)))

theorem sub_constTerm_mem (n : ℕ) (x : K n) :
    x - (constTerm (n+2) x : ℤ) • (1 : K n) ∈ grassmannianIdeal n (n+2) := by
  set I := grassmannianIdeal n (n+2)
  obtain ⟨f, hf⟩ := x
  have hc : f ∈ ElementaryGeneration.elementaryClosure n :=
    ElementaryGeneration.kernel_eq_elementaryClosure n ▸ hf
  have hle := ElementaryGeneration.elementaryClosure_le_kernel n
  revert hf
  induction hc using Subring.closure_induction with
  | mem f hf =>
    obtain ⟨k, hk, _, rfl⟩ := hf
    intro _
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have : constTerm (n+2) (elementaryPoly (n+2) (k+1)) = 0 := constTerm_elementaryPoly _ _
    simp only [this, zero_smul, sub_zero]
    exact eK_mem_top n k
  | zero => intro _; convert I.zero_mem using 1; ext; simp
  | one => intro _; convert I.zero_mem using 1; ext; simp
  | add f g hf hg ihf ihg =>
    intro _
    have h := I.add_mem (ihf (hle hf)) (ihg (hle hg))
    convert h using 1
    apply Subtype.ext
    simp only [map_add, add_smul, Subring.coe_add, AddSubgroupClass.coe_sub, SetLike.val_smul]
    abel
  | neg f hf ihf =>
    intro _
    have h := I.neg_mem (ihf (hle hf))
    convert h using 1
    apply Subtype.ext
    simp only [map_neg, neg_smul, AddSubgroupClass.coe_sub, SetLike.val_smul, Subring.coe_neg]
    abel
  | mul f g hf hg ihf ihg =>
    intro _
    have h := I.add_mem (I.mul_mem_right _ ⟨g, hle hg⟩ (ihf (hle hf)))
      (I.zsmul_mem (constTerm (n+2) f) (ihg (hle hg)))
    convert h using 1
    apply Subtype.ext
    simp only [map_mul, AddSubgroupClass.coe_sub, SetLike.val_smul, Subring.coe_mul,
      Subring.coe_add, OneMemClass.coe_one, sub_mul, smul_mul_assoc, one_mul, smul_sub, mul_smul]
    abel

/-- The constant term on `OΛ_a`. -/
def constK (n : ℕ) : K n →+* ℤ := (constTerm (n+2)).comp (K n).subtype

theorem grassmannianIdeal_top_le_ker (n : ℕ) :
    grassmannianIdeal n (n+2) ≤ TwoSidedIdeal.ker (constK n) := by
  rw [grassmannianIdeal, TwoSidedIdeal.span_le]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ m by omega)
  rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
  exact constTerm_completePoly (n+2) m

theorem constK_apply (n : ℕ) (x : K n) : constK n x = constTerm (n+2) x := rfl

/-- The constant term on `OH_{a,a}`. -/
def constOH (n : ℕ) : OH n (n+2) →+* ℤ :=
  Ideal.Quotient.lift _ (constK n) (fun _ ha =>
    (TwoSidedIdeal.mem_ker _).mp (grassmannianIdeal_top_le_ker n (TwoSidedIdeal.mem_asIdeal.mp ha)))

theorem constOH_toOH (n : ℕ) (x : K n) : constOH n (toOH n (n+2) x) = constK n x := rfl

theorem constOH_injective (n : ℕ) : Function.Injective (constOH n) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := toOH_surjective n (n+2) y
  have h := (toOH_eq_zero_iff n (n+2) _).mpr (sub_constTerm_mem n x)
  rw [constOH_toOH, constK_apply] at hy
  rw [map_sub, map_zsmul, map_one, hy, zero_smul, sub_zero] at h
  exact h

/-- EKL p.44: `OH_{a,a} ≅ ℤ` (here `a = n+2`), via the constant term. -/
def OH_self_equiv (n : ℕ) : OH n (n+2) ≃+* ℤ :=
  RingEquiv.ofBijective (constOH n) ⟨constOH_injective n, fun z => ⟨(z : OH n (n+2)), by simp⟩⟩

/-! ### Errata in the proof of Proposition 5.2: (5.8) and (5.9) -/

theorem grassmannRelation_zero_two_one : grassmannRelation 0 2 1 = eK 0 1 := by
  simp [grassmannRelation, Finset.sum_range_succ]

theorem grassmannRelation_zero_two_two : grassmannRelation 0 2 2 = eK 0 2 := by
  simp [grassmannRelation, Finset.sum_range_succ]

/-- The exponents `C(m,2)` (printed in (5.8)) and `C(m+2,2)` (forced by the induction
hypothesis) always have opposite parity. -/
theorem choose_two_parity (m : ℕ) : (-1 : ℤ)^(m.choose 2) = -(-1)^((m+2).choose 2) := by
  rw [choose_two_add_two, pow_succ, pow_add, pow_mul]; simp

/-- Erratum for (5.8): at `a = N = 2`, `j = 1`, with `M` the printed matrix (5.4) and
`f_{j,0}` the relations (5.6), the printed right side of (5.8) differs from `(M²v)_1`
(they differ by `2ε_2 ≠ 0`). -/
theorem eq_5_8_false :
    ((printedMatrix 0) ^ 2).mulVec (Pi.single 0 1) 0 ≠
      (-1 : ℤ)^((0 : ℕ).choose 2 + (0 : ℕ).choose 2) • (eK 0 1 * grassmannRelation 0 2 1) +
        (-1 : ℤ)^((3 : ℕ).choose 2) • grassmannRelation 0 2 2 := by
  rw [grassmannRelation_zero_two_one, grassmannRelation_zero_two_two]
  intro h
  simp [sq, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, printedMatrix,
    Pi.single_apply] at h
  have h2 := congrArg (fun k : K 0 => ((k : SkewPolynomial 2)) ![1, 1]) h
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_neg, eK_val, AddSubgroupClass.coe_sub,
    Finsupp.add_apply, Finsupp.neg_apply, Finsupp.sub_apply] at h2
  have e2 : elementaryPoly (0+2) 2 = -(generator (0 : Fin 2) * generator 1) :=
    elementaryPoly_two_two
  have h11 : (generator (0 : Fin 2) * generator 1 : SkewPolynomial 2) ![1, 1] = 1 :=
    OddMath.SkewPolynomial.ordered_rank_two_coordinate
  rw [e2, Finsupp.neg_apply, h11] at h2
  omega

/-- `f_{1,m} = -z_{m+1}` (`a = n+2`, `N = a+m`): the lowest relation of (5.6). -/
theorem grassmannRelation_first (n m : ℕ) :
    grassmannRelation n (n+2+m) (m+1) = -zK n (m+1) := by
  rw [grassmannRelation_eq n _ _ (by omega), Finset.sum_range_succ', neg_inj]
  have hc : ¬ (0 ≤ n+2 ∧ m + 1 - 0 ≤ n + 2 + m - (n+2)) := by omega
  rw [if_neg hc]
  simp only [Nat.zero_mul, pow_zero, one_smul, eK_zero, one_mul, Nat.sub_zero]
  rw [add_eq_right]
  apply Finset.sum_eq_zero
  intro k hk
  have := Finset.mem_range.mp hk
  split_ifs with h
  · rfl
  · rw [eK_eq_zero (by omega), zero_mul, smul_zero]

/-- `f_{a,m+1} = (-1)^{a(m+1)} ε_a z_{m+1}`: the top relation of (5.6) for `N+1`. -/
theorem grassmannRelation_top (n m : ℕ) :
    grassmannRelation n (n+2+m+1) (n+2+m+1) = (-1 : ℤ)^((n+2)*(m+1)) • (eK n (n+2) * zK n (m+1)) := by
  rw [grassmannRelation, Finset.sum_eq_single (n+2)]
  · rw [if_pos (by omega), show n + 2 + m + 1 - (n+2) = m+1 by omega]
  · intro k _ hk
    rw [if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- (5.9), second case, corrected: `f_{a,N-a+1} = -(-1)^{a(N-a+1)} ε_a f_{1,N-a}`
(printed: `(-1)^{C(a-1,2)+C(N-a+2,2)} ε_a f_{1,N-a}`). -/
theorem eq_5_9_top (n m : ℕ) :
    grassmannRelation n (n+2+m+1) (n+2+m+1) =
      -((-1 : ℤ)^((n+2)*(m+1)) • (eK n (n+2) * grassmannRelation n (n+2+m) (m+1))) := by
  rw [grassmannRelation_top, grassmannRelation_first, mul_neg, smul_neg, neg_neg]

theorem gen_eq (i : Fin 2) : (generator i : SkewPolynomial 2) = monomial (expSingle i) 1 := rfl

/-- `ε_2 h_3 ≠ 0` for `a = 2`: its coefficient at `x_1^4 x_2` is `1`. -/
theorem coeff_e2_h3 :
    (elementaryPoly 2 2 * completePoly 2 3 : SkewPolynomial 2) ![4, 1] = 1 := by
  rw [elementaryPoly_two_two, completePoly_eq_weakSum]
  simp only [weakSum_succ, weakSum_zero, weakSum_empty, tildeGenerator]
  simp only [gen_eq, mul_one, add_zero, Fin.val_zero, Fin.succ_zero_eq_one, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    mul_add, add_mul, neg_mul, mul_neg, MonomialReversal.monomial_mul_monomial, Finsupp.add_apply, Finsupp.neg_apply]
  simp only [monomial, Finsupp.single_apply]
  decide

/-- Erratum for (5.9), second case: at `a = 2`, `N − a = 2`, the printed
`f_{2,3} = (-1)^{C(1,2)+C(4,2)} ε_2 f_{1,2}` is false; the true sign is `-(-1)^{a(N-a+1)} = -1`
(`eq_5_9_top`) and `ε_2 f_{1,2} ≠ 0`. -/
theorem eq_5_9_false :
    grassmannRelation 0 5 5 ≠
      (-1 : ℤ)^((1 : ℕ).choose 2 + (4 : ℕ).choose 2) • (eK 0 2 * grassmannRelation 0 4 3) := by
  intro h
  have ht := eq_5_9_top 0 2
  rw [ht, grassmannRelation_first] at h
  have hz : zK 0 (2+1) = hK 0 3 := by
    rw [zK]
    norm_num [Nat.choose]
  rw [hz, show ((-1 : ℤ)^((0+2)*(2+1))) = 1 by norm_num,
    show ((-1 : ℤ)^(Nat.choose 1 2 + Nat.choose 4 2)) = 1 by decide] at h
  simp only [one_smul, mul_neg, neg_neg] at h
  have h2 := congrArg (fun k : K 0 => ((k : SkewPolynomial 2)) ![4, 1]) h
  simp only [Subring.coe_neg, Subring.coe_mul, eK_val, hK_val, Finsupp.neg_apply] at h2
  have hc : (elementaryPoly (0+2) 2 * completePoly (0+2) 3 : SkewPolynomial 2) ![4, 1] = 1 :=
    coeff_e2_h3
  rw [hc] at h2
  norm_num at h2

end
end OddMath.Frontier.Cyclotomic

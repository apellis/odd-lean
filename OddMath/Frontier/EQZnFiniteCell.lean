import OddMath.Frontier.EQZnAction
import OddMath.Frontier.EQOddDerivatives
import OddMath.Frontier.EKLSectionTwoH
import OddMath.Frontier.MonomialReversal

/-!
# `Z_n` as a finite-cell right dg module over `OΛ_n`; acyclicity of `Z_n`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.4, (3.37), (3.38), Proposition 3.16 (1) and Proposition 3.17.

`Z_N = OPol_N(0,1,0,1,…)` (strands numbered from `0`, `α_i = {i}`), with differential
`D = dAlpha (zAlpha N)` and right `OΛ_N`-action `x^A 1_z · c = x^A (θ ∘ w₀)(c) 1_z`.

* **(3.37)** (`dAlpha_monomial`, `dAlpha_zAlpha_monomial`): for every exponent vector `A`,
  `d(x^A 1_z) = Σ_i ({A_i} + (-1)^{A_i} α_i) x_i x^A 1_z = Σ_i {A_i + i} x_i x^A 1_z`
  (0-indexed; Ellis–Qi's `{a_i + i - 1}`). Along the way: `d(x^A) = Σ_i {A_i} x_i x^A`,
  `ι(x^A) = (-1)^{|A|} x^A`, `ι(x^A) x_i = (-1)^{A_i} x_i x^A`.
* **The exponent range of `B'_n`.** The printed set `B'_n = {x^a 1_z : 0 ≤ a_i ≤ n - i}` (with
  "`d(x_i^{n-i} 1_z) = 0`") does not span a subcomplex when `n` is even: the `ℤ`-span of the
  staircase monomials is `D`-stable iff `n = 0` or `n` is odd (`staircase_span_stable_iff`).
  The correct range is the reversed staircase `0 ≤ a_i ≤ i - 1` (one-based), i.e. `A_i ≤ i`
  (`RevStair`): its span `U_n` (`EKLSectionTwo.Hrev`) is `D`-stable for every `n`
  (`dAlpha_mem_Hrev`), because the coefficient `{A_i + i}` vanishes when `A_i = i`.
* **Basis** (`zn_right_basis`): `B'_n = {x^A 1_z : A_i ≤ i}` is a basis of `Z_n` as a right
  `OΛ_n`-module (every `f` is uniquely `Σ_A x^A (θ∘w₀)(c_A)` with `c_A ∈ OΛ_n`), for every `n`.
* **Proposition 3.16 (1)** (`prop_3_16_1`): the cell structure. `D(x^A) ∈ span_ℤ{x^B : B ∈ B'_n,
  |B| = |A|+1}`, so the filtration `F_k = span{x^A 1_z · c : |A| ≥ k}` (`cellFiltration`) is a
  finite filtration by dg submodules (`F_0 = Z_n`, `F_k = 0` for `k > n(n-1)/2`), and on
  `F_k / F_{k+1}` the differential is `x^A 1_z · c ↦ (-1)^{|A|} x^A 1_z · d(c)`: each subquotient
  is a direct sum of shifted copies of the regular module `OΛ_n`.
* **(3.38)** (`eq_3_38`): the multiplication map `U_n ⊗_ℤ OΛ_n → Z_n`, `u ⊗ c ↦ u · c`, is a
  bijection, right `OΛ_n`-linear, intertwining the tensor product differential
  `d(u ⊗ c) = d(u) ⊗ c + (-1)^{|u|} u ⊗ d(c)` with `D`; and `U_n` is acyclic for `n ≥ 2`
  (`U_acyclic`, via `∂/∂x_2`).
* **Proposition 3.17** (the acyclicity part, `prop_3_17_acyclic_iff`): `Z_n` is acyclic iff
  `n ≥ 2`; for `n ≤ 1`, `1_z` is a cocycle which is not a coboundary (`D` has no constant term).
  Towards the cofibrancy part (`zn_not_contractible`): for every `n` the identity of `Z_n` has no
  odd left `OPol_n`-linear (a fortiori no left `ONH_n`-linear) null-homotopy.
-/

namespace OddMath.Frontier.EQZn

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) znCellNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) znCellNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {N : ℕ}

/-! ## Monomials -/

theorem generator_mul_monomial (i : Fin N) (A : Fin N → ℕ) :
    generator i * monomial A 1 =
      OddMath.skewSign (expSingle i) A • monomial (expSingle i + A) 1 := by
  rw [OddMath.SkewPolynomial.generator, MonomialReversal.monomial_mul_monomial, one_mul, one_mul,
    OddMath.SkewPolynomial.monomial, OddMath.SkewPolynomial.monomial, Finsupp.smul_single,
    smul_eq_mul, mul_one]

theorem monomial_zero_eq_one : monomial (0 : Fin N → ℕ) 1 = (1 : SkewPolynomial N) := rfl

/-- Peel one variable off a nonconstant monomial: `x^A = ε x_k x^B` with `A = e_k + B`, `ε = ±1`. -/
theorem monomial_peel (A : Fin N → ℕ) (k : Fin N) (hk : A k ≠ 0) :
    ∃ B : Fin N → ℕ, A = expSingle k + B ∧ ∃ ε : ℤ, ε * ε = 1 ∧
      monomial A 1 = ε • (generator k * monomial B 1) := by
  refine ⟨A - expSingle k, ?_, OddMath.skewSign (expSingle k) (A - expSingle k),
    ElementaryGeneration.skewSign_square _ _, ?_⟩
  · funext j
    simp only [Pi.add_apply, Pi.sub_apply, expSingle]
    split_ifs with h
    · subst h; omega
    · omega
  · have hA : expSingle k + (A - expSingle k) = A := by
      funext j
      simp only [Pi.add_apply, Pi.sub_apply, expSingle]
      split_ifs with h
      · subst h; omega
      · omega
    rw [generator_mul_monomial, hA, smul_smul, ElementaryGeneration.skewSign_square, one_smul]

theorem sum_expSingle_add (k : Fin N) (B : Fin N → ℕ) :
    ∑ i, (expSingle k + B) i = ∑ i, B i + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, OddMath.SkewPolynomial.sum_expSingle,
    Finset.mem_univ, ite_true]
  omega

theorem expSingle_add_apply_self (k : Fin N) (B : Fin N → ℕ) : (expSingle k + B) k = B k + 1 := by
  simp [expSingle, add_comm]

theorem expSingle_add_apply_ne {k i : Fin N} (h : i ≠ k) (B : Fin N → ℕ) :
    (expSingle k + B) i = B i := by
  simp [expSingle, Ne.symm h]

/-- The three monomial formulas, proved together by induction on the degree. -/
def MonomialFormulas (A : Fin N → ℕ) : Prop :=
  d N (monomial A 1) = ∑ i, (((A i % 2 : ℕ) : ℤ)) • (generator i * monomial A 1) ∧
  parityInv N (monomial A 1) = (-1 : ℤ) ^ (∑ i, A i) • monomial A 1 ∧
  ∀ i, parityInv N (monomial A 1) * generator i = (-1 : ℤ) ^ (A i) • (generator i * monomial A 1)

theorem monomialFormulas_zero : MonomialFormulas (0 : Fin N → ℕ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [monomial_zero_eq_one]
  · simp [monomial_zero_eq_one]
  · intro i; simp [monomial_zero_eq_one]

theorem coeff_succ_aux (b : ℕ) : ((((b + 1) % 2 : ℕ)) : ℤ) = 1 - ((b % 2 : ℕ) : ℤ) := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [h, show (b + 1) % 2 = 1 by omega]; rfl
  · rw [h, show (b + 1) % 2 = 0 by omega]; rfl

theorem monomialFormulas_step (k : Fin N) (B : Fin N → ℕ) (ε : ℤ)
    (hB : MonomialFormulas B) {A : Fin N → ℕ} (hA : A = expSingle k + B)
    (hx : monomial A 1 = ε • (generator k * monomial B 1)) : MonomialFormulas A := by
  obtain ⟨hd, hι, hιx⟩ := hB
  have anti : ∀ i, i ≠ k → generator i * (generator k * monomial B 1) =
      -(generator k * (generator i * monomial B 1)) := by
    intro i hi
    rw [← mul_assoc, generator_anticomm _ _ hi, neg_mul, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · -- `d(x^A) = Σ {A_i} x_i x^A`
    have key : ∀ i, (((A i % 2 : ℕ) : ℤ)) • (generator i * (ε • (generator k * monomial B 1))) =
        (if i = k then ε • (generator k * generator k * monomial B 1) else 0) -
          ε • ((((B i % 2 : ℕ) : ℤ)) • (generator k * (generator i * monomial B 1))) := by
      intro i
      by_cases hi : i = k
      · subst hi
        rw [hA, expSingle_add_apply_self, coeff_succ_aux, ite_eq_left_iff.mpr (fun h => (h rfl).elim),
          mul_smul_comm, mul_assoc]
        module
      · rw [hA, expSingle_add_apply_ne hi, ite_eq_right_iff.mpr (fun h => (hi h).elim),
          mul_smul_comm, anti i hi]
        module
    rw [hx, map_zsmul, d_mul, d_generator, parityInv_generator, hd,
      Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_add, Finset.smul_sum, neg_mul,
      Finset.mul_sum, mul_smul_comm, smul_neg, Finset.sum_neg_distrib]
    abel
  · -- `ι(x^A) = (-1)^{|A|} x^A`
    rw [hx, map_zsmul, map_mul, parityInv_generator, hι, hA, sum_expSingle_add, pow_succ,
      mul_smul_comm, neg_mul, smul_neg, smul_comm]
    module
  · -- `ι(x^A) x_i = (-1)^{A_i} x_i x^A`
    intro i
    rw [hx, map_zsmul, map_mul, parityInv_generator, smul_mul_assoc]
    simp only [neg_mul, mul_assoc]
    rw [hιx]
    by_cases hi : i = k
    · subst hi
      rw [hA, expSingle_add_apply_self, pow_succ, mul_smul_comm, mul_smul_comm, ← mul_assoc]
      module
    · rw [hA, expSingle_add_apply_ne hi, mul_smul_comm, mul_smul_comm, anti i hi]
      module

theorem monomialFormulas (A : Fin N → ℕ) : MonomialFormulas A := by
  suffices h : ∀ m (A : Fin N → ℕ), ∑ i, A i = m → MonomialFormulas A from h _ A rfl
  intro m
  induction m with
  | zero =>
    intro A hA
    have : A = 0 := funext fun i => by
      have := (Finset.sum_eq_zero_iff.mp hA) i (Finset.mem_univ _); simpa using this
    subst this
    exact monomialFormulas_zero
  | succ m ih =>
    intro A hA
    obtain ⟨k, hk⟩ : ∃ k, A k ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hA
    obtain ⟨B, hAB, ε, _, hx⟩ := monomial_peel A k hk
    refine monomialFormulas_step k B ε (ih B ?_) hAB hx
    rw [hAB, sum_expSingle_add] at hA
    omega

/-- `d(x^A) = Σ_i {A_i} x_i x^A` on `OPol_N` (Ellis–Qi, §3.4, before (3.37)). -/
theorem d_monomial (A : Fin N → ℕ) :
    d N (monomial A 1) = ∑ i, (((A i % 2 : ℕ) : ℤ)) • (generator i * monomial A 1) :=
  (monomialFormulas A).1

theorem parityInv_monomial (A : Fin N → ℕ) :
    parityInv N (monomial A 1) = (-1 : ℤ) ^ (∑ i, A i) • monomial A 1 :=
  (monomialFormulas A).2.1

theorem parityInv_monomial_mul_generator (A : Fin N → ℕ) (i : Fin N) :
    parityInv N (monomial A 1) * generator i = (-1 : ℤ) ^ (A i) • (generator i * monomial A 1) :=
  (monomialFormulas A).2.2 i

/-- **Ellis–Qi (3.37)**, first line, for any `α`:
`d_α(x^A 1_α) = Σ_i ({A_i} + (-1)^{A_i} α_i) x_i x^A 1_α`. -/
theorem dAlpha_monomial (α : Fin N → ℤ) (A : Fin N → ℕ) :
    dAlpha α (monomial A 1) =
      ∑ i, ((((A i % 2 : ℕ) : ℤ)) + (-1 : ℤ) ^ (A i) * α i) • (generator i * monomial A 1) := by
  rw [dAlpha_apply, d_monomial, sAlpha, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, parityInv_monomial_mul_generator, smul_smul, add_smul, mul_comm (α i)]

theorem zAlpha_coeff (a i : ℕ) :
    (((a % 2 : ℕ) : ℤ)) + (-1 : ℤ) ^ a * ((i % 2 : ℕ) : ℤ) = (((a + i) % 2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd i with hi | hi
  · rw [ha.neg_one_pow, Nat.even_iff.mp ha, Nat.even_iff.mp hi, Nat.even_iff.mp (ha.add hi)]; rfl
  · rw [ha.neg_one_pow, Nat.even_iff.mp ha, Nat.odd_iff.mp hi, Nat.odd_iff.mp (ha.add_odd hi)]
    rfl
  · rw [ha.neg_one_pow, Nat.odd_iff.mp ha, Nat.even_iff.mp hi, Nat.odd_iff.mp (ha.add_even hi)]
    rfl
  · rw [ha.neg_one_pow, Nat.odd_iff.mp ha, Nat.odd_iff.mp hi, Nat.even_iff.mp (ha.add_odd hi)]
    rfl

/-- **Ellis–Qi (3.37)** on `Z_N`: `d(x^A 1_z) = Σ_i {A_i + i} x_i x^A 1_z` (0-indexed; Ellis–Qi's
`{a_i + i - 1}`), for every exponent vector `A`. -/
theorem dAlpha_zAlpha_monomial (A : Fin N → ℕ) :
    dAlpha (zAlpha N) (monomial A 1) =
      ∑ i, ((((A i + i.val) % 2 : ℕ) : ℤ)) • (generator i * monomial A 1) := by
  rw [dAlpha_monomial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zAlpha, zAlpha_coeff]


/-! ## The exponent range of `B'_n`: the reversed staircase -/

/-- Exponent vectors of the reversed staircase, `A_i ≤ i` (0-indexed; Ellis–Qi's
`0 ≤ a_i ≤ i - 1`, one-based). -/
def RevStair (N : ℕ) := {A : Fin N → ℕ // ∀ i, A i ≤ i.val}

instance (N : ℕ) : Fintype (RevStair N) := by
  classical
  exact Fintype.ofInjective (fun A : RevStair N =>
    fun i : Fin N => (⟨A.val i, by have h := A.property i; omega⟩ : Fin (N+1)))
    (by intro a b h; apply Subtype.ext; funext i; exact congrArg Fin.val (congrFun h i))

/-- The `ℤ`-span of the monomials `x^B` with `B` in the reversed staircase and `|B| = m`. -/
def revSpan (N m : ℕ) : Submodule ℤ (SkewPolynomial N) :=
  Submodule.span ℤ {f | ∃ B : Fin N → ℕ, (∀ i, B i ≤ i.val) ∧ ∑ i, B i = m ∧ f = monomial B 1}

theorem revSpan_le_Hrev (m : ℕ) : revSpan N m ≤ EKLSectionTwo.Hrev N := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨B, hB, _, rfl⟩
  exact Submodule.subset_span ⟨B, hB, rfl⟩

/-- For `A` in the reversed staircase, `D(x^A 1_z) ∈ span_ℤ{x^B 1_z : B ∈ B'_n, |B| = |A| + 1}`: the
coefficient `{A_i + i}` of `x_i x^A` vanishes exactly when `A_i = i` would leave the range. -/
theorem dAlpha_monomial_mem_revSpan (A : RevStair N) :
    dAlpha (zAlpha N) (monomial A.val 1) ∈ revSpan N (∑ i, A.val i + 1) := by
  rw [dAlpha_zAlpha_monomial]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases h : A.val i = i.val
  · rw [h, show (i.val + i.val) % 2 = 0 by omega]; simp
  · rw [generator_mul_monomial]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨expSingle i + A.val, fun j => ?_, sum_expSingle_add i A.val, rfl⟩))
    by_cases hj : j = i
    · subst hj; rw [expSingle_add_apply_self]; have := A.property j; omega
    · rw [expSingle_add_apply_ne hj]; exact A.property j

/-- **Ellis–Qi, §3.4**: `U_n = span_ℤ(B'_n)` is a subcomplex of `Z_n`, for the reversed staircase
`B'_n = {x^A 1_z : A_i ≤ i}` (one-based `a_i ≤ i - 1`), in every rank. -/
theorem dAlpha_mem_Hrev {f : SkewPolynomial N} (hf : f ∈ EKLSectionTwo.Hrev N) :
    dAlpha (zAlpha N) f ∈ EKLSectionTwo.Hrev N := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    exact revSpan_le_Hrev _ (dAlpha_monomial_mem_revSpan ⟨A, hA⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx

theorem expSingle_add_eq_iff {i j : Fin N} (A : Fin N → ℕ) :
    expSingle i + A = expSingle j + A ↔ i = j := by
  constructor
  · intro h
    have := congrFun h i
    by_contra hij
    simp [expSingle] at this
    exact hij this.symm
  · rintro rfl; rfl

theorem skewSign_expSingle_zero {M : ℕ} (A : Fin (M+1) → ℕ) :
    OddMath.skewSign (expSingle (0 : Fin (M+1))) A = 1 := by
  have h : OddMath.crossingCount (expSingle (0 : Fin (M+1))) A = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_filter] at hj
    by_cases hi : i = 0
    · subst hi; exact absurd hj.2 (Fin.not_lt_zero j)
    · simp [expSingle, Ne.symm hi]
  rw [OddMath.skewSign, h, pow_zero]

/-- The printed exponent range fails for even `n ≥ 2`, and holds otherwise: the `ℤ`-span of the
staircase monomials `x^a 1_z`, `a_i ≤ n - i` (one-based; `SchubertBasis.H`), is `D`-stable iff
`n = 0` or `n` is odd. For even `n ≥ 2`, `D(x_1^{n-1} 1_z)` has the coefficient `1` at
`x_1^n 1_z`. (Contrast `dAlpha_mem_Hrev`.) -/
theorem staircase_span_stable_iff :
    (∀ f ∈ SchubertBasis.H N, dAlpha (zAlpha N) f ∈ SchubertBasis.H N) ↔ (N = 0 ∨ N % 2 = 1) := by
  constructor
  · intro h
    by_contra hN
    push Not at hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    set A : Fin (M+1) → ℕ := fun j => if j = 0 then M else 0
    have hA : ∀ i : Fin (M+1), A i ≤ M + 1 - 1 - i.val := by
      intro i; by_cases hi : i = 0
      · subst hi; simp [A]
      · simp [A, hi]
    have hmem := h _ (Submodule.subset_span ⟨⟨A, hA⟩, rfl⟩)
    rw [SchubertBasis.H_eq_box, SchubertBasis.mem_box] at hmem
    have hval : (dAlpha (zAlpha (M+1)) (StaircaseSpanning.stairMonomial ⟨A, hA⟩))
        (expSingle 0 + A) = 1 := by
      rw [StaircaseSpanning.stairMonomial, dAlpha_zAlpha_monomial, Finsupp.finsetSum_apply,
        Finset.sum_eq_single (0 : Fin (M+1))]
      · rw [generator_mul_monomial, skewSign_expSingle_zero]
        simp only [one_smul, Finsupp.smul_apply, OddMath.SkewPolynomial.monomial,
          Finsupp.single_eq_same, smul_eq_mul, mul_one, Fin.val_zero, add_zero, A, ite_true]
        rw [show M % 2 = 1 by omega]; rfl
      · intro i _ hi
        rw [generator_mul_monomial]
        simp only [Finsupp.smul_apply, OddMath.SkewPolynomial.monomial, Finsupp.single_apply,
          expSingle_add_eq_iff, hi, ite_false, smul_zero]
      · simp
    have := hmem _ (by rw [hval]; exact one_ne_zero) 0
    simp [expSingle, A] at this
  · intro hN f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [StaircaseSpanning.stairMonomial, dAlpha_zAlpha_monomial]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases h : a.val i = N - 1 - i.val
      · have hN' : N % 2 = 1 := by
          rcases hN with h0 | h1
          · have := i.isLt; omega
          · exact h1
        rw [h, show (N - 1 - i.val + i.val) % 2 = 0 by have := i.isLt; omega]; simp
      · rw [generator_mul_monomial]
        have hb : ∀ j, (expSingle i + a.val) j ≤ N - 1 - j.val := by
          intro j
          by_cases hj : j = i
          · subst hj; rw [expSingle_add_apply_self]; have := a.property j; omega
          · rw [expSingle_add_apply_ne hj]; exact a.property j
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hb⟩, rfl⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx


/-! ## `B'_n` is a basis of `Z_n` as a right `OΛ_n`-module -/

section Basis

open SignedPermutation (skewAction)
open LongestElementary (longest)
open StaircaseSpanning (StairIndex stairMonomial)

/-- Reversal of exponent vectors exchanges the reversed staircase and the staircase (EKL (2.46)). -/
def revEquiv (N : ℕ) : RevStair N ≃ StairIndex N where
  toFun A := ⟨fun i => A.val i.rev, fun i => by
    have := A.property i.rev; simp only [Fin.val_rev] at this ⊢; omega⟩
  invFun a := ⟨fun i => a.val i.rev, fun i => by
    have := a.property i.rev; have := i.isLt; simp only [Fin.val_rev] at *; omega⟩
  left_inv A := by apply Subtype.ext; funext i; simp
  right_inv a := by apply Subtype.ext; funext i; simp

theorem neg_one_pow_mul_self' (m : ℕ) : (-1 : ℤ) ^ m * (-1) ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem longest_monomial (A : Fin N → ℕ) : ∃ s : ℤ, s * s = 1 ∧
    skewAction (longest N) (monomial A 1) = s • monomial (fun t => A t.rev) 1 := by
  rw [MonomialReversal.action_monomial, LongestElementary.epsilon_longest, ← pow_mul, ← pow_add]
  exact ⟨_, neg_one_pow_mul_self' _, rfl⟩

theorem longest_revStair (A : RevStair N) : ∃ s : ℤ, s * s = 1 ∧
    skewAction (longest N) (monomial A.val 1) = s • stairMonomial (revEquiv N A) :=
  longest_monomial A.val

/-- Right independence of the reversed staircase over `OΛ̃_N`, every rank. -/
theorem revStair_coeff_zero (c : RevStair N → ElementaryBranching.E N)
    (h : ∑ A, monomial A.val 1 * (c A : SkewPolynomial N) = 0) : ∀ A, c A = 0 := by
  choose s hs hW using longest_revStair (N := N)
  have h' := congrArg (skewAction (longest N)) h
  rw [map_zero, map_sum] at h'
  simp only [map_mul, hW, smul_mul_assoc, ← mul_smul_comm] at h'
  let b : StairIndex N → ElementaryBranching.E N := fun a =>
    ⟨s ((revEquiv N).symm a) • skewAction (longest N) (c ((revEquiv N).symm a)),
      Subring.zsmul_mem _ (EKLSectionTwo.longest_mem_E N _ (c _).property) _⟩
  have hb : ∑ a, stairMonomial a * (b a : SkewPolynomial N) = 0 := by
    rw [← h']
    exact Fintype.sum_equiv (revEquiv N).symm _ _ (fun a => by simp [b])
  have hz := StaircaseIndependence.right_coeff_zero N b hb
  intro A
  have h1 := congrArg Subtype.val (hz (revEquiv N A))
  simp only [b, Equiv.symm_apply_apply, ZeroMemClass.coe_zero] at h1
  have h2 : skewAction (longest N) (c A) = 0 := by
    have := congrArg (fun t => s A • t) h1
    simpa only [smul_smul, hs, one_smul, smul_zero] using this
  apply Subtype.ext
  simpa using h2

/-- Right spanning by the reversed staircase over `OΛ̃_N`, every rank. -/
theorem revStair_span (f : SkewPolynomial N) :
    ∃ c : RevStair N → ElementaryBranching.E N, f = ∑ A, monomial A.val 1 * (c A : SkewPolynomial N) := by
  choose s hs hW using longest_revStair (N := N)
  obtain ⟨c, hc⟩ := StaircaseSpanning.right_span N (skewAction (longest N) f)
  have hf := congrArg (skewAction (longest N)) hc
  rw [LongestElementary.action_involutive, map_sum] at hf
  refine ⟨fun A => ⟨s A • skewAction (longest N) (c (revEquiv N A)),
    Subring.zsmul_mem _ (EKLSectionTwo.longest_mem_E N _ (c _).property) _⟩, ?_⟩
  rw [hf]
  refine Fintype.sum_equiv (revEquiv N).symm _ _ (fun a => ?_)
  obtain ⟨t, ht, hWa⟩ := longest_monomial (N := N) a.val
  have hA := hW ((revEquiv N).symm a)
  simp only [Equiv.apply_symm_apply] at hA
  -- `W(x^a) = t • x^{a ∘ rev}` and `W(x^{a ∘ rev}) = s • x^a`, so `t = s`.
  have hts : t = s ((revEquiv N).symm a) := by
    have e1 : monomial ((revEquiv N).symm a).val 1 = t • skewAction (longest N)
        (stairMonomial a) := by
      rw [StaircaseSpanning.stairMonomial, hWa, smul_smul, ht, one_smul]; rfl
    rw [e1, map_zsmul, LongestElementary.action_involutive] at hA
    have hne : stairMonomial a ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
    have : (t - s ((revEquiv N).symm a)) • stairMonomial a = 0 := by rw [sub_smul, hA, sub_self]
    rcases smul_eq_zero.mp this with h0 | h0
    · omega
    · exact absurd h0 hne
  rw [map_mul, StaircaseSpanning.stairMonomial, hWa]
  change t • monomial (fun t => a.val t.rev) 1 * _ = monomial (fun t => a.val t.rev) 1 *
    (s ((revEquiv N).symm a) • skewAction (longest N) (c (revEquiv N ((revEquiv N).symm a))))
  rw [Equiv.apply_symm_apply, ← hts, smul_mul_assoc, mul_smul_comm]

/-- The reversed staircase monomials form a basis of `OPol_N` as a right `OΛ̃_N`-module. -/
theorem revStair_right_basis (f : SkewPolynomial N) :
    ∃! c : RevStair N → ElementaryBranching.E N,
      f = ∑ A, monomial A.val 1 * (c A : SkewPolynomial N) := by
  obtain ⟨c, hc⟩ := revStair_span f
  refine ⟨c, hc, fun b hb => ?_⟩
  have hz := revStair_coeff_zero (fun A => b A - c A) (by
    show ∑ A, monomial A.val 1 * ((b A : SkewPolynomial N) - (c A : SkewPolynomial N)) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hb, ← hc, sub_self])
  funext A
  exact sub_eq_zero.mp (hz A)

theorem twistRev_leftInverse :
    Function.LeftInverse (fun f => longestPerm N (theta N f)) (twistRev N) := by
  intro f
  have h : ((longestPerm N).comp (theta N)).comp (twistRev N) = RingHom.id _ :=
    ringHom_ext fun j => by
      simp only [RingHom.coe_comp, Function.comp_apply, twistRev_generator, map_zsmul,
        theta_generator, longestPerm_generator, smul_smul, Fin.rev_rev, RingHom.id_apply]
      rw [neg_one_pow_mul_self', one_smul]
  exact RingHom.congr_fun h f

theorem twistRev_injective : Function.Injective (twistRev N) :=
  twistRev_leftInverse.injective

/-- **Ellis–Qi, §3.4** (with the corrected range): `B'_n = {x^A 1_z : A_i ≤ i}` (one-based
`a_i ≤ i - 1`) is a basis of `Z_n` as a right `OΛ_n`-module: every `f 1_z` is uniquely
`Σ_A x^A 1_z · c_A = Σ_A x^A (θ∘w₀)(c_A) 1_z` with `c_A ∈ OΛ_n`. -/
theorem zn_right_basis (f : SkewPolynomial N) :
    ∃! c : RevStair N → osym N, f = ∑ A, monomial A.val 1 * twistRev N (c A) := by
  obtain ⟨e, he, huniq⟩ := revStair_right_basis f
  have hpre : ∀ A, ∃ c ∈ osym N, twistRev N c = (e A : SkewPolynomial N) := by
    intro A
    have h : (e A : SkewPolynomial N) ∈ (osym N).map (twistRev N) := by
      rw [map_twistRev_osym]; exact (e A).property
    exact h
  choose c hc hce using hpre
  refine ⟨fun A => ⟨c A, hc A⟩, ?_, fun b hb => ?_⟩
  · simp only [hce]; exact he
  · have hbe := huniq (fun A => ⟨twistRev N (b A), twistRev_mem_E (b A).property⟩) hb
    funext A
    apply Subtype.ext
    apply twistRev_injective (N := N)
    have := congrArg (fun g => (g A : SkewPolynomial N)) hbe
    simpa [hce] using this

end Basis

/-! ## Proposition 3.16 (1): the cell filtration -/

/-- The cell filtration `F_k = span{x^A 1_z · c : A ∈ B'_n, |A| ≥ k, c ∈ OΛ_n}` of `Z_n`. -/
def cellFiltration (N k : ℕ) : Submodule ℤ (SkewPolynomial N) :=
  Submodule.span ℤ {f | ∃ A : RevStair N, k ≤ ∑ i, A.val i ∧ ∃ c ∈ osym N,
    f = monomial A.val 1 * twistRev N c}

theorem mem_cellFiltration (A : RevStair N) {k : ℕ} (hk : k ≤ ∑ i, A.val i) {c : SkewPolynomial N}
    (hc : c ∈ osym N) : monomial A.val 1 * twistRev N c ∈ cellFiltration N k :=
  Submodule.subset_span ⟨A, hk, c, hc, rfl⟩

theorem revSpan_mul_mem {m : ℕ} {g : SkewPolynomial N} (hg : g ∈ revSpan N m)
    {c : SkewPolynomial N} (hc : c ∈ osym N) : g * twistRev N c ∈ cellFiltration N m := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨B, hB, hBm, rfl⟩ := hx
    exact mem_cellFiltration ⟨B, hB⟩ hBm.ge hc
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem cellFiltration_antitone {k l : ℕ} (h : k ≤ l) : cellFiltration N l ≤ cellFiltration N k := by
  refine Submodule.span_mono ?_
  rintro _ ⟨A, hA, c, hc, rfl⟩
  exact ⟨A, h.trans hA, c, hc, rfl⟩

/-- The cell differential: for `|A| = k`,
`D(x^A 1_z · c) ≡ (-1)^k x^A 1_z · d(c)` modulo `F_{k+1}`. -/
theorem dAlpha_cell (A : RevStair N) {c : SkewPolynomial N} (hc : c ∈ osym N) :
    dAlpha (zAlpha N) (monomial A.val 1 * twistRev N c) -
      (-1 : ℤ) ^ (∑ i, A.val i) • (monomial A.val 1 * twistRev N (d N c)) ∈
        cellFiltration N (∑ i, A.val i + 1) := by
  rw [dAlpha_mul_twistRev, parityInv_monomial, smul_mul_assoc, add_sub_cancel_right]
  exact revSpan_mul_mem (dAlpha_monomial_mem_revSpan A) hc

/-- **Ellis–Qi, Proposition 3.16 (1)**: `Z_n` is a finite-cell right dg module over `OΛ_n`.
The filtration `F_k` (`cellFiltration`) satisfies: `F_0 = Z_n`; `F_k = 0` for
`k > n(n-1)/2`; `F_{k+1} ⊆ F_k`; each `F_k` is a dg submodule (stable under `D` and under the
right `OΛ_n`-action); and on `F_k / F_{k+1}` the differential is
`x^A 1_z · c ↦ (-1)^k x^A 1_z · d(c)` (`dAlpha_cell`), so by `zn_right_basis` each subquotient is
free with basis `{x^A 1_z : A ∈ B'_n, |A| = k}`, a direct sum of shifted copies of the regular
right dg module `OΛ_n`. -/
theorem prop_3_16_1 :
    cellFiltration N 0 = ⊤ ∧
    (∀ k, N * (N - 1) / 2 < k → cellFiltration N k = ⊥) ∧
    (∀ k, cellFiltration N (k+1) ≤ cellFiltration N k) ∧
    (∀ k f, f ∈ cellFiltration N k → dAlpha (zAlpha N) f ∈ cellFiltration N k) ∧
    (∀ k f c, f ∈ cellFiltration N k → c ∈ osym N → f * twistRev N c ∈ cellFiltration N k) := by
  refine ⟨?_, ?_, fun k => cellFiltration_antitone (Nat.le_succ k), ?_, ?_⟩
  · rw [eq_top_iff]
    intro f _
    obtain ⟨c, hc, _⟩ := zn_right_basis f
    rw [hc]
    exact Submodule.sum_mem _ fun A _ => mem_cellFiltration A (Nat.zero_le _) (c A).property
  · intro k hk
    rw [cellFiltration, Submodule.span_eq_bot]
    rintro _ ⟨A, hA, c, hc, rfl⟩
    exfalso
    have hsum : ∑ i, A.val i ≤ ∑ i : Fin N, i.val := Finset.sum_le_sum fun i _ => A.property i
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id] at hsum
    omega
  · intro k f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨A, hA, c, hc, rfl⟩ := hx
      have h := dAlpha_cell A hc
      have h2 : (-1 : ℤ) ^ (∑ i, A.val i) • (monomial A.val 1 * twistRev N (d N c)) ∈
          cellFiltration N k :=
        Submodule.smul_mem _ _ (mem_cellFiltration A hA (d_mem_osym hc))
      have h3 := cellFiltration_antitone (N := N) (show k ≤ ∑ i, A.val i + 1 by omega) h
      simpa using add_mem h3 h2
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx
  · intro k f c hf hc
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨A, hA, c', hc', rfl⟩ := hx
      rw [mul_assoc, ← map_mul]
      exact mem_cellFiltration A hA (mul_mem hc' hc)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

/-! ## Proposition 3.17: acyclicity of `Z_n` -/

/-- `d_α` has no constant term: `(d_α f)(0) = 0` for every `f` and every `α`. -/
theorem dAlpha_apply_zero (α : Fin N → ℤ) (f : SkewPolynomial N) : (dAlpha α f) 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single A c =>
    rw [← Finsupp.smul_single_one, map_zsmul, Finsupp.smul_apply]
    change c • (dAlpha α (monomial A 1)) 0 = 0
    rw [dAlpha_monomial, Finsupp.finsetSum_apply, Finset.sum_eq_zero, smul_zero]
    intro i _
    have hne : (0 : Fin N → ℕ) ≠ expSingle i + A := by
      intro h
      have := congrFun h i
      simp [expSingle] at this
      omega
    rw [generator_mul_monomial]
    simp [hne]

theorem sAlpha_zAlpha_small (hN : N ≤ 1) : sAlpha (zAlpha N) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : i.val = 0 := by have := i.isLt; omega
  simp [zAlpha, hi]

/-- For `n ≤ 1`, `1_z` is a cocycle of `Z_n` which is not a coboundary. -/
theorem zn_not_acyclic (hN : N ≤ 1) :
    dAlpha (zAlpha N) 1 = 0 ∧ ∀ g, dAlpha (zAlpha N) g ≠ 1 := by
  refine ⟨?_, fun g hg => ?_⟩
  · rw [dAlpha_apply, d_one, map_one, one_mul, sAlpha_zAlpha_small hN, zero_add]
  · have h := dAlpha_apply_zero (zAlpha N) g
    rw [hg] at h
    exact EKLSectionTwo.one_apply_zero N h

/-- **Ellis–Qi, Proposition 3.17** (the acyclicity statements): `Z_n` is acyclic as a complex
iff `n ≥ 2`. For `n ≥ 2` the odd derivative `∂/∂x_2` (0-indexed `x_1`, with `α_1 = 1`) is a
null-homotopy of the identity (Corollary 3.15); for `n ≤ 1`, see `zn_not_acyclic`. -/
theorem prop_3_17_acyclic_iff :
    (∀ f, dAlpha (zAlpha N) f = 0 → ∃ g, dAlpha (zAlpha N) g = f) ↔ 2 ≤ N := by
  constructor
  · intro h
    by_contra hN
    obtain ⟨g, hg⟩ := h 1 (zn_not_acyclic (by omega)).1
    exact (zn_not_acyclic (by omega)).2 g hg
  · intro hN f hf
    exact ⟨pd N ⟨1, hN⟩ f, acyclic (zAlpha N) ⟨1, hN⟩ (by simp [zAlpha]) hf⟩


/-- Left multiplication by a generator has no constant term. -/
theorem generator_mul_apply_zero (i : Fin N) (f : SkewPolynomial N) : (generator i * f) 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add, Finsupp.add_apply, hf, hg, add_zero]
  | single A c =>
    rw [← Finsupp.smul_single_one, mul_smul_comm, Finsupp.smul_apply]
    change c • (generator i * monomial A 1) 0 = 0
    have hne : (0 : Fin N → ℕ) ≠ expSingle i + A := by
      intro h
      have := congrFun h i
      simp [expSingle] at this
      omega
    rw [generator_mul_monomial]
    simp [hne]

/-- Towards the cofibrancy part of **Ellis–Qi, Proposition 3.17**: for every `n`, the identity
of `Z_n` has no null-homotopy which is odd and left `OPol_n`-linear (`h(x_j f) = -x_j h(f)`),
a fortiori none which is left `ONH_n`-linear. Such an `h` is `h(g) = ι(g) k` with `k = h(1_z)`,
and `(D h + h D)(1_z) = D(k) - s k` has no constant term. Hence for `n ≥ 2` the acyclic module
`Z_n` is not contractible as a left dg `ONH_n`-module; since an acyclic cofibrant dg module is
contractible, `Z_n` is not cofibrant over `ONH_n` for `n ≥ 2`. -/
theorem zn_not_contractible :
    ¬ ∃ h : SkewPolynomial N →+ SkewPolynomial N,
      (∀ j f, h (generator j * f) = -(generator j * h f)) ∧
      ∀ f, dAlpha (zAlpha N) (h f) + h (dAlpha (zAlpha N) f) = f := by
  rintro ⟨h, hlin, hhom⟩
  -- `T = h ∘ ι` commutes with left multiplication, hence is right multiplication by `T 1`.
  have hT : ∀ g f, h (parityInv N (g * f)) = g * h (parityInv N f) := by
    intro g
    induction g using induction_generator with
    | hgen j => intro f; rw [map_mul, parityInv_generator, neg_mul, map_neg, hlin, neg_neg]
    | h0 => intro f; simp
    | h1 => intro f; simp
    | hadd a b ha hb => intro f; rw [add_mul, map_add, map_add, ha, hb, add_mul]
    | hneg a ha => intro f; rw [neg_mul, map_neg, map_neg, ha, neg_mul]
    | hmul a b ha hb => intro f; rw [mul_assoc, ha, hb, mul_assoc]
  have hform : ∀ g, h g = parityInv N g * h 1 := by
    intro g
    have := hT (parityInv N g) 1
    rwa [mul_one, parityInv_parityInv, map_one] at this
  have h1 := hhom 1
  have hD1 : dAlpha (zAlpha N) 1 = sAlpha (zAlpha N) := by
    rw [dAlpha_apply, d_one, map_one, one_mul, zero_add]
  rw [hform (dAlpha (zAlpha N) 1), hD1, parityInv_sAlpha, neg_mul] at h1
  have h0 := congrArg (fun p : SkewPolynomial N => p 0) h1
  simp only [Finsupp.add_apply, Finsupp.neg_apply, dAlpha_apply_zero, zero_add] at h0
  have hs : (sAlpha (zAlpha N) * h 1) 0 = 0 := by
    rw [sAlpha, Finset.sum_mul, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_mul_assoc, Finsupp.smul_apply, generator_mul_apply_zero, smul_zero]
  rw [hs, neg_zero] at h0
  exact EKLSectionTwo.one_apply_zero N h0.symm

/-! ## `U_n` and the decomposition `Z_n ≅ U_n ⊗ OΛ_n` (3.38) -/

section Tensor

open SchubertBasis (Box mem_box monomial_mem_box box_mul box_mono)
open scoped TensorProduct

theorem box_le_Hrev {A : Fin N → ℕ} (hA : ∀ i, A i ≤ i.val) : Box A ≤ EKLSectionTwo.Hrev N := by
  intro f hf
  rw [mem_box] at hf
  have he : f = ∑ a ∈ f.support, f a • monomial a 1 := by
    simpa only [Finsupp.sum, OddMath.SkewPolynomial.monomial, Finsupp.smul_single, smul_eq_mul,
      mul_one] using (Finsupp.sum_single f).symm
  rw [he]
  refine Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨a, fun i => (hf a (Finsupp.mem_support_iff.mp ha) i).trans (hA i), rfl⟩)

/-- The odd derivative `∂/∂x_i` lowers exponents: `∂/∂x_i (x^A)` is supported on exponents `≤ A`. -/
theorem pd_monomial_mem_box (i : Fin N) (A : Fin N → ℕ) : pd N i (monomial A 1) ∈ Box A := by
  suffices h : ∀ m (A : Fin N → ℕ), ∑ j, A j = m → pd N i (monomial A 1) ∈ Box A from h _ A rfl
  intro m
  induction m with
  | zero =>
    intro A hA
    have : A = 0 := funext fun j => by
      have := (Finset.sum_eq_zero_iff.mp hA) j (Finset.mem_univ _); simpa using this
    subst this
    rw [monomial_zero_eq_one, D_one (parityInv N) (pd N i) (pd_mul i)]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro A hA
    obtain ⟨k, hk⟩ : ∃ k, A k ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hA
    obtain ⟨B, hAB, ε, _, hx⟩ := monomial_peel A k hk
    have hB : pd N i (monomial B 1) ∈ Box B := ih B (by rw [hAB, sum_expSingle_add] at hA; omega)
    have hBA : ∀ j, B j ≤ A j := fun j => by rw [hAB]; simp only [Pi.add_apply]; omega
    rw [hx, map_zsmul, pd_mul, pd_generator, parityInv_generator, neg_mul]
    refine Submodule.smul_mem _ _ (add_mem ?_ (neg_mem ?_))
    · split_ifs
      · rw [one_mul]; exact box_mono hBA (monomial_mem_box _ _ _ fun _ => le_rfl)
      · rw [zero_mul]; exact Submodule.zero_mem _
    · have := box_mul (monomial_mem_box (expSingle k) (expSingle k) 1 fun _ => le_rfl) hB
      rwa [← hAB] at this

theorem pd_mem_Hrev (i : Fin N) {f : SkewPolynomial N} (hf : f ∈ EKLSectionTwo.Hrev N) :
    pd N i f ∈ EKLSectionTwo.Hrev N := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    exact box_le_Hrev hA (pd_monomial_mem_box i A)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx

theorem parityInv_mem_Hrev {f : SkewPolynomial N} (hf : f ∈ EKLSectionTwo.Hrev N) :
    parityInv N f ∈ EKLSectionTwo.Hrev N := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    rw [parityInv_monomial]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨A, hA, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx

/-- **Ellis–Qi, §3.4**: `U_n` is an acyclic complex for `n ≥ 2`: `∂/∂x_2` (0-indexed `x_1`)
preserves `U_n` and is a null-homotopy of its identity. -/
theorem U_acyclic (hN : 2 ≤ N) {f : SkewPolynomial N} (hf : f ∈ EKLSectionTwo.Hrev N)
    (hd : dAlpha (zAlpha N) f = 0) :
    pd N ⟨1, hN⟩ f ∈ EKLSectionTwo.Hrev N ∧ dAlpha (zAlpha N) (pd N ⟨1, hN⟩ f) = f :=
  ⟨pd_mem_Hrev _ hf, acyclic (zAlpha N) ⟨1, hN⟩ (by simp [zAlpha]) hd⟩

/-- The basis `B'_n` of `U_n` over `ℤ`. -/
def uBasis (N : ℕ) : Module.Basis (RevStair N) ℤ (EKLSectionTwo.Hrev N) :=
  have hli : LinearIndependent ℤ (fun A : RevStair N => (monomial A.val 1 : SkewPolynomial N)) :=
    (Finsupp.basisSingleOne (R := ℤ) (ι := Fin N → ℕ)).linearIndependent.comp _
      Subtype.val_injective
  have hspan : Submodule.span ℤ (Set.range fun A : RevStair N =>
      (monomial A.val 1 : SkewPolynomial N)) = EKLSectionTwo.Hrev N := by
    unfold EKLSectionTwo.Hrev
    congr 1
    ext f
    constructor
    · rintro ⟨A, rfl⟩; exact ⟨A.val, A.property, rfl⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨⟨A, hA⟩, rfl⟩
  (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)

theorem uBasis_apply (A : RevStair N) : (uBasis N A : SkewPolynomial N) = monomial A.val 1 := by
  simp [uBasis, Module.Basis.span_apply]

/-- The multiplication map `U_n ⊗ OΛ_n → Z_n`, `u ⊗ c ↦ u · c = u (θ∘w₀)(c) 1_z`. -/
def tensorMap (N : ℕ) : EKLSectionTwo.Hrev N ⊗[ℤ] osym N →ₗ[ℤ] SkewPolynomial N :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun c => (u : SkewPolynomial N) * twistRev N c
          map_add' := fun a b => by
            simp only [Subring.coe_add, map_add, mul_add]
          map_smul' := fun r a => by
            simp only [AddSubgroupClass.coe_zsmul, map_zsmul, mul_smul_comm, RingHom.id_apply] }
      map_add' := fun a b => by
        ext c; simp only [Submodule.coe_add, add_mul, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.add_apply]
      map_smul' := fun r a => by
        ext c; simp only [SetLike.val_smul, smul_mul_assoc, LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, LinearMap.smul_apply] }

theorem tensorMap_tmul (u : EKLSectionTwo.Hrev N) (c : osym N) :
    tensorMap N (u ⊗ₜ c) = (u : SkewPolynomial N) * twistRev N c := rfl

/-- The differential of `U_n`. -/
def dU (N : ℕ) : EKLSectionTwo.Hrev N →ₗ[ℤ] EKLSectionTwo.Hrev N where
  toFun u := ⟨dAlpha (zAlpha N) u, dAlpha_mem_Hrev u.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_zsmul _ _ _)

/-- The parity involution of `U_n`. -/
def iotaU (N : ℕ) : EKLSectionTwo.Hrev N →ₗ[ℤ] EKLSectionTwo.Hrev N where
  toFun u := ⟨parityInv N u, parityInv_mem_Hrev u.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_zsmul _ _ _)

/-- The differential of `OΛ_n` (Lemma 3.2). -/
def dO (N : ℕ) : osym N →ₗ[ℤ] osym N where
  toFun c := ⟨d N c, d_mem_osym c.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_zsmul _ _ _)

/-- The tensor product differential `d(u ⊗ c) = d(u) ⊗ c + (-1)^{|u|} u ⊗ d(c)` on
`U_n ⊗ OΛ_n` (the sign recorded by `ι`). -/
def dTensor (N : ℕ) : EKLSectionTwo.Hrev N ⊗[ℤ] osym N →ₗ[ℤ] EKLSectionTwo.Hrev N ⊗[ℤ] osym N :=
  TensorProduct.map (dU N) LinearMap.id + TensorProduct.map (iotaU N) (dO N)

/-- **Ellis–Qi (3.38)**: `Z_n ≅ U_n ⊗ OΛ_n` as right dg `OΛ_n`-modules. The multiplication map
`u ⊗ c ↦ u · c` is bijective, right `OΛ_n`-linear, and intertwines the tensor product
differential with the differential of `Z_n`. -/
theorem eq_3_38 :
    Function.Bijective (tensorMap N) ∧
    (∀ t, tensorMap N (dTensor N t) = dAlpha (zAlpha N) (tensorMap N t)) ∧
    (∀ t (c : osym N), tensorMap N (TensorProduct.map LinearMap.id (LinearMap.mulRight ℤ c) t) =
      tensorMap N t * twistRev N c) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- injectivity, from the uniqueness in `zn_right_basis`
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    set e := TensorProduct.equivFinsuppOfBasisLeft (uBasis N) (N := osym N)
    have ht' : t = (e t).sum fun A n => uBasis N A ⊗ₜ n := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
    have hsum : tensorMap N t = ∑ A, monomial A.val 1 * twistRev N (e t A) := by
      conv_lhs => rw [ht']
      rw [map_finsuppSum, Finsupp.sum_fintype _ _ (by intro A; simp)]
      simp only [tensorMap_tmul, uBasis_apply]
    rw [ht] at hsum
    obtain ⟨c0, _, huniq⟩ := zn_right_basis (0 : SkewPolynomial N)
    have h1 := huniq (fun A => e t A) hsum
    have h0 := huniq (fun _ => 0) (by simp)
    have het : e t = 0 := by
      refine Finsupp.ext fun A => ?_
      have := congrFun (h1.trans h0.symm) A
      simpa using this
    rw [← e.symm_apply_apply t, het, map_zero]
  · -- surjectivity, from the existence in `zn_right_basis`
    intro f
    obtain ⟨c, hc, _⟩ := zn_right_basis f
    refine ⟨∑ A, uBasis N A ⊗ₜ c A, ?_⟩
    rw [map_sum, hc]
    simp only [tensorMap_tmul, uBasis_apply]
  · intro t
    induction t with
    | tmul u c =>
      simp only [dTensor, LinearMap.add_apply, TensorProduct.map_tmul, map_add, tensorMap_tmul,
        LinearMap.id_apply]
      exact (dAlpha_mul_twistRev (u : SkewPolynomial N) c).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro t c
    induction t with
    | tmul u c' =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulRight_apply,
        tensorMap_tmul, Subring.coe_mul, map_mul, mul_assoc]
    | add x y hx hy => simp only [map_add, hx, hy, add_mul]

end Tensor

end

end OddMath.Frontier.EQZn

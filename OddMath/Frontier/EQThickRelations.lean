import OddMath.Frontier.EQThickSplitters
import OddMath.Frontier.EQSchurDifferential
import OddMath.Frontier.CenterONHControls

/-!
# Ellis–Qi §4.1: relations of the odd thick calculus in the Ellis–Qi convention

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §4.1 and §4.2.1 (displayed equations; printed numbering).

Ambient ring `ONH_{n+2} = NilHeckeAction.Presented n`, `N = n + 2`, `0`-indexed strands, a written
product `x * y` is `x` drawn on top of `y`, `e_N = (-1)^{C(N,3)} ∂_{w_0} x^δ` (`eqIdempotent`), and
`w_0` is the plain permutation action `x_i ↦ x_{N-1-i}` (`EQSkewDifferential.longestPerm`,
Ellis–Qi §2.3).  The twisted odd elementary polynomials `ẽ_k = θ(e_k)` are EKL's
`elementaryPoly N k` (Ellis–Qi Remark 2.9), and `OΛ̃_N` is the joint kernel `K n` of the `∂_i`.

* `thick_mul_thick` (§4.1): `e_N f e_N g e_N = e_N f g e_N` for `g ∈ OΛ̃_N` (any `f`).
* §4.1, "Equation (2.64) of [EKL] implies `∂_{w_0} f = w_0(f) ∂_{w_0}`": with Ellis–Qi's plain
  `w_0` this is off by a sign.  The correct statement is
  `∂_{w_0} f = (-1)^{C(N,2) p(f)} w_0(f) ∂_{w_0}` for `f ∈ OΛ̃_N` of parity `p(f)`
  (`DElem_mul_poly`); EKL's `w_0` is the signed action.  The literal statement fails for `N = 2`,
  `f = ẽ_1` (`DElem_mul_poly_printed_false`).
* §4.1, the "convenient relation" `e_N x_1 ⋯ x_k e_N = ẽ_k e_N` holds only up to the sign
  `(-1)^{C(k,2)}`: `e_N x_1 ⋯ x_k e_N = (-1)^{C(k,2)} ẽ_k e_N` for `0 ≤ k ≤ N`
  (`convenient_relation`); the printed form fails for `N = 2`, `k = 2`
  (`convenient_relation_printed_false`).  For `k ≤ 1` the printed form holds.
* §4.1, exploder composition: `∂_{w_0} f e_N = e_N ∂_{w_0}(f) e_N` for every `f ∈ OPol_N`
  (`exploder_composition`), and its specialization
  `∂_{w_0} x^λ x^δ e_N = (-1)^{C(N,3) + C(N,2)|λ|} e_N w_0(s̃_λ) e_N` (`exploder_schur`; any
  exponent vector `λ`), with `s̃_λ` the twisted odd Schur polynomial (3.25)
  (`EQSchur.twisted`).
* §4.2.1: `e_N x_i e_N = ∂_{w_0}(x^δ x_i) ∂_{w_0} x^δ` (`eqIdempotent_dot_eqIdempotent_eq`).
* Remark 4.1: `e_N` is the image of EKL's idempotent under the word-reversal
  anti-automorphism (`remark_4_1`).
-/

namespace OddMath.Frontier.EQThick

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis ZeroHecke OnhWindow ThickBubble
open OddMath.Diagrams.OddNilHecke (dONH eqIdempotent)
open OnhPolynomial (polyElem action_polyElem)
open EQSkewDifferential (longestPerm parityInv)
open FiniteCompleteElementary
open scoped BigOperators

noncomputable section

variable {n : ℕ}

theorem action_eqIdempotent_apply_kernel {g h : SkewPolynomial (n + 2)} (hh : h ∈ K n) :
    action n (eqIdempotent n) (g * h) = action n (eqIdempotent n) g * h :=
  NilHeckeRightKernel.action_right_mul n _ _ hh g

/-! ## Decorated thick strands -/

/-- Ellis–Qi §4.1: `e_N f e_N g e_N = e_N f g e_N` for `g ∈ OΛ̃_N` (and any `f ∈ OPol_N`). -/
theorem thick_mul_thick (f : SkewPolynomial (n + 2)) {g : SkewPolynomial (n + 2)} (hg : g ∈ K n) :
    eqIdempotent n * polyElem n f * eqIdempotent n * polyElem n g * eqIdempotent n =
      eqIdempotent n * polyElem n (f * g) * eqIdempotent n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro p
  simp only [action_mul_apply, action_polyElem]
  rw [action_eqIdempotent_kernel (Subring.mul_mem _ hg (action_eqIdempotent_mem p))]
  exact congrArg _ (OddMath.SkewPolynomial.mul_assoc f g _).symm

/-! ## `∂_{w_0} f = ± w_0(f) ∂_{w_0}` -/

/-- Corrected §4.1 relation (EKL (2.64) in Ellis–Qi's notation): for `f ∈ OΛ̃_N` of parity `k`,
`∂_{w_0} f = (-1)^{C(N,2) k} w_0(f) ∂_{w_0}` with the plain permutation action `w_0`. -/
theorem DElem_mul_poly {f : SkewPolynomial (n + 2)} (hf : f ∈ K n) (k : ℕ)
    (hk : parityInv (n + 2) f = (-1 : ℤ) ^ k • f) :
    DElem n * polyElem n f =
      (-1 : ℤ) ^ ((n + 2).choose 2 * k) • (polyElem n (longestPerm (n + 2) f) * DElem n) := by
  rw [OnhPolynomial.DElem_poly_kernel f hf, EQSchur.skewAction_longest f k hk, map_zsmul,
    smul_mul_assoc]

theorem coeff_eq_zero_of_eq_neg {N : ℕ} {f : SkewPolynomial N} (h : f = -f) (c : Fin N → ℕ) :
    f c = 0 := by
  have := congrArg (fun p : SkewPolynomial N => p c) h
  simp only [Finsupp.neg_apply] at this
  omega

/-- The literal §4.1 statement `∂_{w_0} f = w_0(f) ∂_{w_0}` (plain `w_0`) fails for `N = 2`,
`f = ẽ_1 = x_1 - x_2`: here `∂_{w_0} ẽ_1 = ẽ_1 ∂_{w_0}` while `w_0(ẽ_1) = -ẽ_1`. -/
theorem DElem_mul_poly_printed_false :
    DElem 0 * polyElem 0 (elementaryPoly 2 1) ≠
      polyElem 0 (longestPerm 2 (elementaryPoly 2 1)) * DElem 0 := by
  intro h
  have hw : longestPerm 2 (elementaryPoly 2 1) = -elementaryPoly 2 1 := by
    rw [CenterONHControls.e1_rankTwo, map_sub, EQSkewDifferential.longestPerm_generator,
      EQSkewDifferential.longestPerm_generator, neg_sub]
    rfl
  have hc : etElem 0 * DElem 0 = DElem 0 * etElem 0 := by
    have := etElem_mul_DElem 0
    norm_num at this
    exact this
  rw [← polyElem_elementary_one] at hc
  rw [hw, map_neg, neg_mul, ← hc] at h
  have h2 := congrArg (fun z => action 0 z (generator 0)) h
  simp only [action_mul_apply, action_polyElem, ZeroHecke.action_DElem, map_neg,
    LinearMap.neg_apply] at h2
  have hD : LongestDivided.D 2 (generator 0) = 1 := by
    simp [LongestDivided.D, LongestDivided.wordIn, LongestDivided.coxeterWord,
      LongestDivided.applyWord, AllRankDivided.divided_generator]
  rw [hD, mul_one] at h2
  have := coeff_eq_zero_of_eq_neg h2 (OddMath.SkewPolynomial.expSingle 0)
  rw [CenterONHControls.e1_rankTwo] at this
  have hne : OddMath.SkewPolynomial.expSingle (1 : Fin 2) ≠ OddMath.SkewPolynomial.expSingle 0 :=
    fun he => by
      have := congrFun he 0
      simp [OddMath.SkewPolynomial.expSingle] at this
  simp [OddMath.SkewPolynomial.generator, hne] at this

/-! ## The relation `e_N x_1 ⋯ x_k e_N = ± ẽ_k e_N` -/

/-- The ordered product of dots `x_1 x_2 ⋯ x_k` (Ellis–Qi's indices; strands `0, …, k-1`). -/
def dotRun (n k : ℕ) : Presented n := dotMonomial fun i => if i.val < k then 1 else 0

/-- `∂_{w_0}(x^δ x_I) = 0` when `I` contains an index `j ≥ 1` with `j - 1 ∉ I`. -/
theorem D_staircase_subset {I : Finset (Fin (n + 2))} {j : Fin (n + 2)} (hj : j ∈ I)
    (hj1 : 1 ≤ j.val) (hjI : ∀ i : Fin (n + 2), i.val + 1 = j.val → i ∉ I) :
    LongestDivided.D (n + 2)
      (LongestDivided.staircase (n + 2) * monomial (OddSchurPieri.subsetExp I) 1) = 0 := by
  obtain ⟨L, ε, -, hD⟩ := LongestFactor.D_factor_first n ⟨j.val - 1, by omega⟩
  have hi : (⟨j.val - 1, by omega⟩ : Fin (n + 2)) ∉ I := hjI _ (by simp; omega)
  rw [hD, LinearMap.smul_apply, LinearMap.comp_apply, LongestDivided.staircase,
    MonomialReversal.monomial_mul_monomial, ShuffleLemma.divided_monomial_balanced, map_zero,
    smul_zero]
  have hj' : (Fin.succ ⟨j.val - 1, by omega⟩ : Fin (n + 2)) = j := Fin.ext (by simp; omega)
  have hi' : (Fin.castSucc ⟨j.val - 1, by omega⟩ : Fin (n + 2)) = ⟨j.val - 1, by omega⟩ := rfl
  simp only [Pi.add_apply, OddSchurPieri.subsetExp, hj', hi', hj, hi, ↓reduceIte]
  omega

/-- A set `I` of strands closed under `j ↦ j - 1` is an initial segment `{0, …, |I| - 1}`. -/
theorem subset_eq_initial {I : Finset (Fin (n + 2))}
    (hI : ∀ j ∈ I, 1 ≤ j.val → ∃ i ∈ I, i.val + 1 = j.val) :
    I = Finset.univ.filter fun i : Fin (n + 2) => i.val < I.card := by
  have hdown : ∀ d : ℕ, ∀ j ∈ I, ∀ i : Fin (n + 2), i.val + d = j.val → i ∈ I := by
    intro d
    induction d with
    | zero => intro j hj i h; rwa [show i = j from Fin.ext (by omega)]
    | succ d ih =>
      intro j hj i h
      obtain ⟨i', hi', hi'j⟩ := hI j hj (by omega)
      exact ih i' hi' i (by omega)
  have hanti : Antitone (OddSchurPieri.subsetExp I) := by
    intro i j hij
    simp only [OddSchurPieri.subsetExp]
    by_cases hj : j ∈ I
    · have hi : i ∈ I := hdown (j.val - i.val) j hj i (by rw [Fin.le_def] at hij; omega)
      simp [hj, hi]
    · simp [hj]
  have he := OddSchurPieri.antitone_subset I hanti
  ext i
  have := congrFun he i
  simp only [OddSchurPieri.subsetExp] at this
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : i ∈ I <;> by_cases h2 : i.val < I.card <;> simp_all

theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k N : ℕ} (hk : k ≤ N) :
    ∑ i ∈ Finset.range N, (if i < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- `(-1)^{C(N,3)} ∂_{w_0}(x^δ x_1 ⋯ x_k) = (-1)^{C(k,2)} ẽ_k` for `k ≤ N`. -/
theorem D_staircase_column (k : ℕ) (hk : k ≤ n + 2) :
    (-1 : ℤ) ^ (n + 2).choose 3 • LongestDivided.D (n + 2) (LongestDivided.staircase (n + 2) *
      monomial (fun i => if i.val < k then 1 else 0) 1) =
      (-1 : ℤ) ^ k.choose 2 • elementaryPoly (n + 2) k := by
  set I₀ : Finset (Fin (n + 2)) := Finset.univ.filter fun i => i.val < k with hI₀
  set X := (-1 : ℤ) ^ (n + 2).choose 3 • LongestDivided.D (n + 2)
    (LongestDivided.staircase (n + 2) * monomial (fun i => if i.val < k then 1 else 0) 1) with hX
  have hcard : I₀.card = k := by
    rw [hI₀, Fin.card_filter_val_lt]; omega
  have hE := action_eqIdempotent_kernel (OddSymmetricKernel.elementary_mem n k)
  rw [action_eqIdempotent] at hE
  have hsum : (-1 : ℤ) ^ (n + 2).choose 3 • LongestDivided.D (n + 2)
      (LongestDivided.staircase (n + 2) * elementaryPoly (n + 2) k) = (-1 : ℤ) ^ k.choose 2 • X := by
    rw [← action_staircaseElem_apply, OddSchurPieri.elementary_subsets, map_sum, map_sum,
      Finset.smul_sum, Finset.sum_eq_single I₀]
    · rw [OddSchurPieri.subsetTilde, map_zsmul, map_zsmul, smul_comm, hX,
        action_staircaseElem_apply,
        show OddSchurPieri.subsetExp I₀ = fun i => if i.val < k then 1 else 0 from by
          funext i; simp [OddSchurPieri.subsetExp, hI₀],
        show OddSchurPieri.tildeWeight I₀ = k.choose 2 from by
          rw [OddSchurPieri.tildeWeight, hI₀, Finset.sum_filter,
            Fin.sum_univ_eq_sum_range (fun i => if i < k then i else 0), sum_range_ite_lt _ hk,
            Finset.sum_range_id, Nat.choose_two_right]]
    · intro I hI hne
      rw [Finset.mem_filter] at hI
      by_cases hbad : ∃ j ∈ I, 1 ≤ j.val ∧ ∀ i : Fin (n + 2), i.val + 1 = j.val → i ∉ I
      · obtain ⟨j, hj, hj1, hjI⟩ := hbad
        rw [OddSchurPieri.subsetTilde, map_zsmul, map_zsmul, action_staircaseElem_apply,
          D_staircase_subset hj hj1 hjI, smul_zero, smul_zero]
      · exfalso
        apply hne
        rw [subset_eq_initial (I := I) fun j hj hj1 => by
          by_contra hc
          exact hbad ⟨j, hj, hj1, fun i hi hiI => hc ⟨i, hiI, hi⟩⟩, hI.2]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ I₀, hcard⟩) h
  rw [hsum] at hE
  rw [← hE, smul_smul, neg_one_pow_mul_self, one_smul]

/-- **Ellis–Qi §4.1**, corrected: `e_N x_1 ⋯ x_k e_N = (-1)^{C(k,2)} ẽ_k e_N` for `k ≤ N`. -/
theorem convenient_relation (k : ℕ) (hk : k ≤ n + 2) :
    eqIdempotent n * dotRun n k * eqIdempotent n =
      (-1 : ℤ) ^ k.choose 2 • (polyElem n (elementaryPoly (n + 2) k) * eqIdempotent n) := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro p
  rw [action_mul_apply, action_mul_apply, dotRun, action_dotMonomial,
    action_eqIdempotent_apply_kernel (action_eqIdempotent_mem p), action_eqIdempotent,
    D_staircase_column k hk, map_zsmul, LinearMap.smul_apply, action_mul_apply, action_polyElem,
    smul_mul_assoc]

theorem elementary_two_two : elementaryPoly 2 2 (fun _ => 1) = -1 := by
  rw [OddSchurPieri.elementary_subsets,
    show (Finset.univ.filter fun I : Finset (Fin 2) => I.card = 2) = {Finset.univ} by decide,
    Finset.sum_singleton, OddSchurPieri.subsetTilde, OddSchurPieri.tildeWeight]
  have hs : OddSchurPieri.subsetExp (Finset.univ : Finset (Fin 2)) = fun _ => 1 := by
    funext i; simp [OddSchurPieri.subsetExp]
  simp [hs, Fin.sum_univ_two]

/-- The printed form `e_N x_1 ⋯ x_k e_N = ẽ_k e_N` fails for `N = 2`, `k = 2`. -/
theorem convenient_relation_printed_false :
    eqIdempotent 0 * dotRun 0 2 * eqIdempotent 0 ≠
      polyElem 0 (elementaryPoly 2 2) * eqIdempotent 0 := by
  intro h
  rw [convenient_relation 2 le_rfl, show Nat.choose 2 2 = 1 by rfl, pow_one, neg_one_smul] at h
  have h2 := congrArg (fun z => action 0 z 1) h
  simp only [map_neg, LinearMap.neg_apply, action_mul_apply, action_eqIdempotent_one,
    action_polyElem, mul_one] at h2
  have := coeff_eq_zero_of_eq_neg h2.symm (fun _ => 1)
  rw [elementary_two_two] at this
  exact absurd this (by norm_num)

/-! ## Exploders -/

/-- **Ellis–Qi §4.1**: exploding a thick strand, decorating the thin strands by `f` and merging
again gives the thick strand decorated by `∂_{w_0}(f)`: `∂_{w_0} f e_N = e_N ∂_{w_0}(f) e_N`. -/
theorem exploder_composition (f : SkewPolynomial (n + 2)) :
    DElem n * polyElem n f * eqIdempotent n =
      eqIdempotent n * polyElem n (LongestDivided.D (n + 2) f) * eqIdempotent n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro p
  simp only [action_mul_apply, action_polyElem, ZeroHecke.action_DElem]
  rw [LongestDivided.D_right_kernel n _ _ (action_eqIdempotent_mem p),
    action_eqIdempotent_kernel (Subring.mul_mem _ (LongestKernel.D_mem_kernel n f)
      (action_eqIdempotent_mem p))]

/-- **Ellis–Qi §4.1**: `∂_{w_0} x^λ x^δ e_N = (-1)^{C(N,3) + C(N,2)|λ|} e_N w_0(s̃_λ) e_N`, with
`s̃_λ` the twisted odd Schur polynomial (3.25) (any exponent vector `λ`). -/
theorem exploder_schur (a : Fin (n + 2) → ℕ) :
    DElem n * polyElem n (monomial a 1 * LongestDivided.staircase (n + 2)) * eqIdempotent n =
      (-1 : ℤ) ^ ((n + 2).choose 3 + (n + 2).choose 2 * ∑ j, a j) •
        (eqIdempotent n * polyElem n (longestPerm (n + 2) (EQSchur.twisted (n + 2) a)) *
          eqIdempotent n) := by
  rw [exploder_composition, EQSchur.twisted, map_zsmul, EQSchur.longestPerm_longestPerm,
    map_zsmul, mul_smul_comm, smul_mul_assoc, smul_smul, neg_one_pow_mul_self, one_smul]

/-- Ellis–Qi §4.2.1: `e_N x_i e_N = ∂_{w_0}(x^δ x_i) ∂_{w_0} x^δ`. -/
theorem eqIdempotent_dot_eqIdempotent_eq (i : Fin (n + 2)) :
    eqIdempotent n * dot n i * eqIdempotent n =
      polyElem n (LongestDivided.D (n + 2) (LongestDivided.staircase (n + 2) * generator i)) *
        (DElem n * staircaseElem n) := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro p
  rw [action_mul_apply, action_mul_apply, action_dot_apply,
    action_eqIdempotent_apply_kernel (action_eqIdempotent_mem p), action_eqIdempotent,
    action_eqIdempotent, action_mul_apply, action_polyElem, action_mul_apply,
    ZeroHecke.action_DElem, action_staircaseElem_apply, smul_mul_assoc, mul_smul_comm, smul_smul,
    neg_one_pow_mul_self, one_smul]

/-- Ellis–Qi Remark 4.1: the Ellis–Qi idempotent `(-1)^{C(N,3)} ∂_{w_0} x^δ` is the reflection
about a horizontal axis (the word-reversal anti-automorphism) of EKL's
`(-1)^{C(N,3)} x^δ ∂_{w_0}` (`ZeroHecke.projector`). -/
theorem remark_4_1 :
    NilHeckeRightBasis.reverseLinear n (projector n) = eqIdempotent n := by
  rw [prop_3_5, map_zsmul, NilHeckeRightBasis.reverse_mul, reverse_DElem',
    show NilHeckeRightBasis.reverseLinear n (staircaseElem n) =
      (-1 : ℤ) ^ (n + 2).choose 4 • staircaseElem n from OnhReflection.reverse_staircaseElem n,
    smul_mul_smul_comm, smul_smul, neg_one_pow_mul_self, mul_one, eqIdempotent_eq_zsmul]

end

end OddMath.Frontier.EQThick

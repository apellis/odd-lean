import OddMath.Frontier.EQSchurModule
import OddMath.Frontier.ThickDots
import OddMath.Frontier.OddSchurPieri
import OddMath.Frontier.ShuffleLemma
import OddMath.Frontier.SmallRank

/-!
# The differential of an odd Schur polynomial

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.3, (3.24)–(3.29), Remark 3.10 and Proposition 3.11 (printed numbering); (2.21), (2.39).

Strands are numbered from `0`: `θ(x_i) = (-1)^i x_i` (Ellis–Qi's `(-1)^{i-1}`), `w_0(x_i) =
x_{N-1-i}` (plain permutation action), `x^δ = x_0^{N-1} x_1^{N-2} ⋯ x_{N-2}`, and
`∂_{w_0} = ∂_0(∂_1∂_0)⋯(∂_{N-2}⋯∂_0)` is `LongestDivided.D N` (Ellis–Qi's choice (2.39)). An
exponent vector `a : Fin N → ℕ` gives the ordered monomial `x^a = x_0^{a_0} ⋯ x_{N-1}^{a_{N-1}}`;
partitions of length `≤ N` are the antitone `a`.

* `untwisted N a` : the untwisted odd Schur polynomial (3.24), `s_a = w_0 θ ∂_{w_0}(x̃^δ x̃^a)`
  with `x̃ = θ(x)`;
* `twisted N a` : the twisted odd Schur polynomial (3.25),
  `s̃_a = (-1)^{binom(N,3) + binom(N,2)|a|} w_0 ∂_{w_0}(x^a x^δ)`.

Main results:

* `d_untwisted` : for **every** exponent vector `a` (not only partitions),
  `d(s_a) = Σ_i (-1)^{|a/i| + i} {a_i - i} s_{a + ε_i}`, where `|a/i| = Σ_{j<i} a_j` and
  `{m} = m mod 2`;
* `prop_3_11` (**Ellis–Qi, Proposition 3.11**, (3.29)): for a partition `λ` of length `≤ N`,
  `d(s_λ) = Σ_{μ = λ + □_i} (-1)^{|λ/i| + i - 1} {ct(□_i)} s_μ` (1-indexed rows in the paper;
  here the row `i` is `0`-indexed, so the sign is `(-1)^{|λ/i| + i}` and `ct(□_i) = λ_i - i`).
  Adding a box in row `N` (0-indexed), i.e. beyond length `N`, does not occur;
* `twisted_eq_theta_untwisted` ((3.27)): `s̃_a = θ(s_a)`; `sz_relation_left`,
  `sz_relation_right` ((3.28), the SZ relations `z s_a = (-1)^{(N+1)|a|} w_0(s̃_a) z`,
  `s̃_a z = z w_0(s_a)` for the right action `z f = (θ ∘ w_0)(f) z` of (3.19));
  `theta_longestPerm` ((2.21)); the parities `parityInv_untwisted`, `parityInv_twisted`;
* Remark 3.10: `twisted_eq_ekl`, `twisted_eq_schurAll` (`s̃_a` is EKL's odd Schur polynomial,
  EKL (4.17) = (2.69), in every rank);
* examples for `N = 2`: `untwisted_one_eq` (`s_{(1)} = x_1 + x_2`), `twisted_one_eq`,
  `d_untwisted_one` (`d s_{(1)} = s_{(2)} + s_{(1,1)}`), `d_untwisted_one_one`
  (`d s_{(1,1)} = s_{(2,1)}`), `d_untwisted_two` (`d s_{(2)} = -s_{(2,1)}`).

All statements are over `ℤ` (Ellis–Qi work over a field `𝕜`; the identities are integral).

The proof follows Ellis–Qi: the Schur-through-`z` relation `z s_a = θ w_0 (s_a) z` and
Lemma 3.5 on `Z_N` (`dZ_D_staircase`) reduce `d(s_a)` to `d_z(x^a) = d(x^a) + ι(x^a) s`, whose
coefficient on `x^{a + ε_i}` is `(-1)^{|a/i|}({a_i} + (-1)^{a_i}{i}) = (-1)^{|a/i|}{a_i - i}`;
the terms with `a + ε_i` not a partition vanish since `∂_{w_0}` kills a monomial with two equal
adjacent exponents.
-/

namespace OddMath.Frontier.EQSchur

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNUNASemiringSchurD (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARingSchurD (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## Products of powers in a ring with an odd derivation -/

section Generic

variable {R : Type*} [Ring R]

theorem prod_ofFn_zsmul : ∀ {m : ℕ} (c : Fin m → ℤ) (f : Fin m → R),
    (List.ofFn fun j => c j • f j).prod = (∏ j, c j) • (List.ofFn f).prod
  | 0, c, f => by simp
  | m+1, c, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_zsmul (fun j => c j.succ) (fun j => f j.succ),
      Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]

theorem iota_pow (ι : R →+* R) (y : R) (hy : ι y = -y) (k : ℕ) :
    ι (y ^ k) = (-1 : ℤ) ^ k • y ^ k := by
  rw [map_pow, hy, neg_pow, zsmul_eq_mul]
  push_cast
  rfl

theorem D_pow (ι : R →+* R) (D : R →+ R) (hD : ∀ a b, D (a * b) = D a * b + ι a * D b)
    (y : R) (hy : ι y = -y) (hDy : D y = y * y) :
    ∀ k : ℕ, D (y ^ k) = ((k % 2 : ℕ) : ℤ) • y ^ (k + 1)
  | 0 => by simp [D_one ι D hD]
  | k + 1 => by
    rw [pow_succ', hD, hDy, hy, D_pow ι D hD y hy hDy k, neg_mul, mul_smul_comm, ← pow_succ',
      mul_assoc, ← pow_succ', ← pow_succ']
    have hq : (((k + 1) % 2 : ℕ) : ℤ) = 1 - ((k % 2 : ℕ) : ℤ) := by omega
    rw [hq, sub_smul, one_smul, sub_eq_add_neg]

/-- The odd Leibniz rule on an ordered product of powers `y_0^{a_0} ⋯ y_{m-1}^{a_{m-1}}` of
`ι`-odd elements with `D(y_j) = y_j²`: raising the `i`-th exponent by one, with the sign
`(-1)^{a_0 + ⋯ + a_{i-1}}` and the coefficient `{a_i}`. -/
theorem D_prod_pow (ι : R →+* R) (D : R →+ R) (hD : ∀ a b, D (a * b) = D a * b + ι a * D b) :
    ∀ {m : ℕ} (y : Fin m → R), (∀ j, ι (y j) = -y j) → (∀ j, D (y j) = y j * y j) →
      ∀ a : Fin m → ℕ, D (List.ofFn fun j => y j ^ a j).prod =
        ∑ i, ((-1 : ℤ) ^ (∑ j, if j < i then a j else 0) * ((a i % 2 : ℕ) : ℤ)) •
          (List.ofFn fun j => y j ^ (a + expSingle i) j).prod
  | 0, y, _, _, a => by simp [D_one ι D hD]
  | m + 1, y, hy, hDy, a => by
    rw [List.ofFn_succ, List.prod_cons, hD, D_pow ι D hD _ (hy 0) (hDy 0), iota_pow ι _ (hy 0),
      D_prod_pow ι D hD (fun j => y j.succ) (fun j => hy _) (fun j => hDy _) (fun j => a j.succ),
      Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.not_lt_zero, ite_false, Finset.sum_const_zero, pow_zero, one_mul,
        List.ofFn_succ, List.prod_cons, Pi.add_apply, expSingle, ite_true, smul_mul_assoc]
      congr 4
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [List.ofFn_succ, List.prod_cons, Pi.add_apply, expSingle, Fin.sum_univ_succ,
        Fin.succ_pos, ite_true, Fin.succ_lt_succ_iff, smul_mul_assoc, mul_smul_comm, smul_smul,
        Fin.succ_inj]
      congr 1
      rw [pow_add]
      ring

end Generic

variable {N : ℕ}

/-! ## Monomials -/

/-- `|a/i| = Σ_{j<i} a_j`: the number of boxes in the rows above row `i` (Ellis–Qi's `|λ/i|`,
rows numbered from `0`). -/
def rowsAbove (a : Fin N → ℕ) (i : Fin N) : ℕ := ∑ j ∈ Finset.univ.filter (· < i), a j

theorem rowsAbove_eq (a : Fin N → ℕ) (i : Fin N) :
    rowsAbove a i = ∑ j, if j < i then a j else 0 := by
  rw [rowsAbove, Finset.sum_filter]

/-- The content `ct = (column) - (row)` of the box added to row `i` of `a` (both numbered from
`0` or both from `1`): `a_i - i`. -/
def content (a : Fin N → ℕ) (i : Fin N) : ℤ := (a i : ℤ) - i.val

/-- `d(x^a) = Σ_i (-1)^{|a/i|} {a_i} x^{a + ε_i}`. -/
theorem d_monomial (a : Fin N → ℕ) :
    d N (monomial a 1) =
      ∑ i, ((-1 : ℤ) ^ rowsAbove a i * ((a i % 2 : ℕ) : ℤ)) • monomial (a + expSingle i) 1 := by
  simp_rw [MonomialReversal.monomial_eq_prod]
  rw [D_prod_pow (parityInv N) (d N) d_mul generator (fun j => parityInv_generator j)
    (fun j => d_generator j)]
  simp only [rowsAbove_eq]

theorem map_monomial_diag (ψ : SkewPolynomial N →+* SkewPolynomial N) (c : Fin N → ℤ)
    (hψ : ∀ j, ψ (generator j) = c j • generator j) (a : Fin N → ℕ) :
    ψ (monomial a 1) = (∏ j, c j ^ a j) • monomial a 1 := by
  rw [MonomialReversal.monomial_eq_prod, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow, hψ, smul_pow]
  rw [prod_ofFn_zsmul]

/-- `θ(x^a) = (-1)^{Σ_j j a_j} x^a`. -/
theorem theta_monomial (a : Fin N → ℕ) :
    theta N (monomial a 1) = (-1 : ℤ) ^ (∑ j, j.val * a j) • monomial a 1 := by
  rw [map_monomial_diag (theta N) (fun j => (-1 : ℤ) ^ j.val) theta_generator]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]

/-- `ι(x^a) = (-1)^{|a|} x^a`. -/
theorem parityInv_monomial (a : Fin N → ℕ) :
    parityInv N (monomial a 1) = (-1 : ℤ) ^ (∑ j, a j) • monomial a 1 := by
  rw [map_monomial_diag (parityInv N) (fun _ => (-1 : ℤ)) (fun j => by simp)]
  simp only [Finset.prod_pow_eq_pow_sum]

theorem crossingCount_expSingle (a : Fin N → ℕ) (i : Fin N) :
    OddMath.crossingCount a (expSingle i) = ∑ k, if i < k then a k else 0 := by
  unfold OddMath.crossingCount
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [expSingle, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem sum_split (a : Fin N → ℕ) (i : Fin N) :
    ∑ j, a j = (∑ j, if j < i then a j else 0) + a i + ∑ j, if i < j then a j else 0 := by
  have h : ∀ j, a j = (if j < i then a j else 0) + (if j = i then a j else 0) +
      (if i < j then a j else 0) := by
    intro j
    rcases lt_trichotomy j i with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  conv_lhs => rw [Finset.sum_congr rfl fun j _ => h j]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem parity_identity (p i : ℕ) :
    ((p % 2 : ℕ) : ℤ) + (-1 : ℤ) ^ p * ((i % 2 : ℕ) : ℤ) = ((p : ℤ) - i) % 2 := by
  rcases Nat.even_or_odd p with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [Even.neg_one_pow ⟨r, rfl⟩]; omega
  · rw [Odd.neg_one_pow ⟨r, rfl⟩]; omega

/-- `d_z(x^a) = d(x^a) + ι(x^a) s = Σ_i (-1)^{|a/i|} {a_i - i} x^{a + ε_i}` on `Z_N`. -/
theorem dZ_monomial (a : Fin N → ℕ) :
    dZ N (monomial a 1) =
      ∑ i, ((-1 : ℤ) ^ rowsAbove a i * (content a i % 2)) • monomial (a + expSingle i) 1 := by
  rw [dZ, dAlpha_apply, d_monomial, parityInv_monomial, sAlpha, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, zAlpha, show generator i = monomial (expSingle i) 1 from rfl,
    OddSchurPieri.mono_mul, smul_smul, smul_smul, ← add_smul, OddMath.skewSign,
    crossingCount_expSingle, content, ← parity_identity, rowsAbove_eq]
  congr 1
  rw [sum_split a i]
  have hT : ∀ T : ℕ, ((-1 : ℤ) ^ T) * (-1) ^ T = 1 := fun T => by rw [← mul_pow]; norm_num
  linear_combination ((-1 : ℤ) ^ ((∑ j, if j < i then a j else 0) + a i) *
    (((i : ℕ) % 2 : ℕ) : ℤ)) * hT (∑ k, if i < k then a k else 0)

/-! ## Odd Schur polynomials -/

/-- The staircase exponent `δ = (N-1, N-2, …, 1, 0)`. -/
def delta (N : ℕ) : Fin N → ℕ := fun i => N - 1 - i.val

theorem staircase_eq_monomial (N : ℕ) : LongestDivided.staircase N = monomial (delta N) 1 := rfl

/-- **Ellis–Qi (3.24)**: the untwisted odd Schur polynomial
`s_a = w_0 θ ∂_{w_0}(x̃^δ x̃^a)`, `x̃ = θ(x)`, for an exponent vector `a` (a partition of length
`≤ N` when `a` is antitone). -/
def untwisted (N : ℕ) (a : Fin N → ℕ) : SkewPolynomial N :=
  longestPerm N (theta N (LongestDivided.D N
    (theta N (LongestDivided.staircase N) * theta N (monomial a 1))))

/-- **Ellis–Qi (3.25)**: the twisted odd Schur polynomial
`s̃_a = (-1)^{binom(N,3) + binom(N,2)|a|} w_0 ∂_{w_0}(x^a x^δ)`. -/
def twisted (N : ℕ) (a : Fin N → ℕ) : SkewPolynomial N :=
  (-1 : ℤ) ^ (N.choose 3 + N.choose 2 * ∑ j, a j) •
    longestPerm N (LongestDivided.D N (monomial a 1 * LongestDivided.staircase N))

theorem theta_theta (f : SkewPolynomial N) : theta N (theta N f) = f := by
  have h : (theta N).comp (theta N) = RingHom.id _ := ringHom_ext fun j => by
    simp only [RingHom.comp_apply, theta_generator, map_zsmul, smul_smul, ← mul_pow,
      RingHom.id_apply]
    norm_num
  exact RingHom.congr_fun h f

theorem longestPerm_longestPerm (f : SkewPolynomial N) : longestPerm N (longestPerm N f) = f := by
  have h : (longestPerm N).comp (longestPerm N) = RingHom.id _ := ringHom_ext fun j => by
    simp
  exact RingHom.congr_fun h f

theorem twistRev_injective : Function.Injective (twistRev N) := by
  intro f g h
  have := congrArg (fun x => longestPerm N (theta N x)) h
  simpa only [twistRev, RingHom.comp_apply, theta_theta, longestPerm_longestPerm] using this

/-- The weight `Σ_j j a_j`, so that `θ(x^a) = (-1)^{Σ_j j a_j} x^a`. -/
def weight (a : Fin N → ℕ) : ℕ := ∑ j, j.val * a j

theorem weight_add_expSingle (a : Fin N → ℕ) (i : Fin N) :
    weight (a + expSingle i) = weight a + i.val := by
  simp [weight, mul_add, Finset.sum_add_distrib, expSingle, mul_ite, Finset.sum_ite_eq]

/-- The Schur-through-`z` relation in the form used for Proposition 3.11:
`θ w_0 (s_a) = ∂_{w_0}(x̃^δ x̃^a) = (-1)^{Σ j δ_j + Σ j a_j} ∂_{w_0}(x^δ x^a)`. -/
theorem twistRev_untwisted (a : Fin N → ℕ) :
    twistRev N (untwisted N a) = (-1 : ℤ) ^ (weight (delta N) + weight a) •
      LongestDivided.D N (LongestDivided.staircase N * monomial a 1) := by
  rw [twistRev, RingHom.comp_apply, untwisted, longestPerm_longestPerm, theta_theta,
    staircase_eq_monomial, theta_monomial, theta_monomial, smul_mul_smul_comm, map_zsmul,
    ← pow_add]
  rfl

/-- **Ellis–Qi, Lemma 3.5 on `Z_N`** in every rank:
`d_z(∂_{w_0}(x^δ g)) - ∂_{w_0}(x^δ d_z(g)) = s ∂_{w_0}(x^δ g)` with `s = Σ_i {i} x_i`. -/
theorem dZ_D_staircase (N : ℕ) (g : SkewPolynomial N) :
    dZ N (LongestDivided.D N (LongestDivided.staircase N * g)) -
        LongestDivided.D N (LongestDivided.staircase N * dZ N g) =
      sZ N * LongestDivided.D N (LongestDivided.staircase N * g) := by
  rcases N with _ | _ | n
  · simp [SmallRank.D_small, SmallRank.staircase_small, sZ, sAlpha]
  · have hs : sZ 1 = 0 := by simp [sZ, sAlpha, zAlpha]
    simp [SmallRank.D_small, SmallRank.staircase_small, hs]
  · exact dZ_D_staircase_add_two g

/-- The differential of an untwisted odd Schur polynomial, for **every** exponent vector `a`:
`d(s_a) = Σ_i (-1)^{|a/i| + i} {a_i - i} s_{a + ε_i}` (rows numbered from `0`). -/
theorem d_untwisted (a : Fin N → ℕ) :
    d N (untwisted N a) =
      ∑ i, ((-1 : ℤ) ^ (rowsAbove a i + i.val) * (content a i % 2)) •
        untwisted N (a + expSingle i) := by
  apply twistRev_injective
  set G := LongestDivided.D N (LongestDivided.staircase N * monomial a 1) with hG
  set S := sZ N
  have h1 := d_twistRev (untwisted N a)
  have h2 : twistRev N (d N (untwisted N a)) = d N (twistRev N (untwisted N a)) -
      S * twistRev N (untwisted N a) + parityInv N (twistRev N (untwisted N a)) * S := by
    rw [h1]; abel
  have hK := dZ_D_staircase N (monomial a 1)
  rw [dZ, dAlpha_apply, ← hG] at hK
  have e : LongestDivided.D N (LongestDivided.staircase N * dZ N (monomial a 1)) =
      d N G - S * G + parityInv N G * S := by
    rw [← sub_eq_zero, ← hK]; abel
  rw [h2, twistRev_untwisted, ← hG, map_zsmul, map_zsmul, smul_mul_assoc, mul_smul_comm,
    ← smul_sub, ← smul_add, ← e, dZ_monomial, Finset.mul_sum, map_sum, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, twistRev_untwisted, mul_smul_comm, map_zsmul, smul_smul, smul_smul,
    weight_add_expSingle]
  congr 1
  have hi : ((-1 : ℤ) ^ i.val) * (-1) ^ i.val = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(content a i % 2 * (-1) ^ weight (delta N) * (-1) ^ weight a *
    (-1) ^ rowsAbove a i)) * hi

/-- `∂_{w_0}` kills `x^δ x^a` when `δ + a` has two equal adjacent exponents, i.e.
`a_{j+1} = a_j + 1`; hence `s_a = 0`. -/
theorem untwisted_eq_zero_of_step {n : ℕ} (a : Fin (n+2) → ℕ) (j : Fin (n+1))
    (h : a j.succ = a j.castSucc + 1) : untwisted (n+2) a = 0 := by
  rw [untwisted, staircase_eq_monomial, theta_monomial, theta_monomial, smul_mul_smul_comm,
    OddSchurPieri.mono_mul, smul_smul, map_zsmul,
    OddSchurPieri.D_of_divided_zero j _ (ShuffleLemma.divided_monomial_balanced j _ 1 ?_),
    smul_zero, map_zero, map_zero]
  simp only [Pi.add_apply, delta, Fin.val_castSucc, Fin.val_succ, h]
  omega

/-- If `λ` is a partition but `λ + ε_i` is not, then `i ≥ 1` and `λ_{i-1} = λ_i`. -/
theorem exists_step_of_not_antitone {n : ℕ} {l : Fin (n+2) → ℕ} (hl : Antitone l)
    {i : Fin (n+2)} (h : ¬ Antitone (l + expSingle i)) :
    ∃ j : Fin (n+1), j.succ = i ∧ l j.castSucc = l i := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  apply h
  intro p q hpq
  simp only [Pi.add_apply, expSingle]
  by_cases hq : i = q
  · subst hq
    by_cases hp : i = p
    · subst hp; exact le_rfl
    · have hpi : p.val < i.val := lt_of_le_of_ne hpq (fun e => hp (Fin.ext e.symm))
      let j : Fin (n+1) := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have h1 := hne j hj
      have h2 : l j.castSucc ≤ l p := hl (by rw [Fin.le_def]; simp [j]; omega)
      have h3 : l i ≤ l j.castSucc := hl (by rw [Fin.le_def]; simp [j])
      simp only [ite_true, hp, ite_false]
      omega
  · have := hl hpq
    simp only [hq, ite_false]
    split_ifs <;> omega

open Classical in
/-- **Ellis–Qi, Proposition 3.11** (3.29): for a partition `λ` of length at most `N`,
`d(s_λ) = Σ_{μ = λ + □_i} (-1)^{|λ/i| + i - 1} {ct(□_i)} s_μ`.
Rows are numbered from `0` here, so Ellis–Qi's row `i` is our row `i - 1`: the sign reads
`(-1)^{|λ/i| + i}` with `|λ/i| = Σ_{j<i} λ_j` (`rowsAbove`), and the content of the added box is
`ct(□_i) = λ_i - i` (`content`); `{m} = m mod 2`. The sum runs over the rows `i < N` for which
`λ + □_i` is again a partition; no box is added in a row beyond the `N`-th. -/
theorem prop_3_11 (l : Fin N → ℕ) (hl : Antitone l) :
    d N (untwisted N l) =
      ∑ i, if Antitone (l + expSingle i) then
        ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (content l i % 2)) • untwisted N (l + expSingle i)
      else 0 := by
  rw [d_untwisted]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rcases N with _ | _ | n
    · exact i.elim0
    · exact absurd (fun p q _ => le_of_eq (congrArg _
        (Fin.ext (by have := p.isLt; have := q.isLt; omega)))) h
    · obtain ⟨j, rfl, hjl⟩ := exists_step_of_not_antitone hl h
      rw [untwisted_eq_zero_of_step _ j, smul_zero]
      simp [expSingle, hjl, (Fin.castSucc_lt_succ (i := j)).ne']

/-! ## Parity, `θ ∘ w_0` versus `w_0 ∘ θ`, and the signed action -/

theorem parityInv_theta (f : SkewPolynomial N) :
    parityInv N (theta N f) = theta N (parityInv N f) := by
  have h : (parityInv N).comp (theta N) = (theta N).comp (parityInv N) :=
    ringHom_ext fun j => by simp
  exact RingHom.congr_fun h f

theorem parityInv_longestPerm (f : SkewPolynomial N) :
    parityInv N (longestPerm N f) = longestPerm N (parityInv N f) := by
  have h : (parityInv N).comp (longestPerm N) = (longestPerm N).comp (parityInv N) :=
    ringHom_ext fun j => by simp
  exact RingHom.congr_fun h f

theorem neg_one_pow_congr {p q : ℕ} (h : p % 2 = q % 2) : (-1 : ℤ) ^ p = (-1) ^ q := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-- **Ellis–Qi (2.21)**: `(θ ∘ w_0)(f) = (-1)^{(N+1) p(f)} (w_0 ∘ θ)(f)` for `f` of parity `k`
(`ι f = (-1)^k f`). -/
theorem theta_longestPerm (f : SkewPolynomial N) (k : ℕ)
    (hf : parityInv N f = (-1 : ℤ) ^ k • f) :
    theta N (longestPerm N f) = (-1 : ℤ) ^ ((N + 1) * k) • longestPerm N (theta N f) := by
  rcases Nat.even_or_odd (N + 1) with hN | hN
  · have h : (theta N).comp (longestPerm N) = (longestPerm N).comp (theta N) :=
      ringHom_ext fun j => by
        simp only [RingHom.comp_apply, longestPerm_generator, theta_generator, map_zsmul]
        congr 1
        obtain ⟨r, hr⟩ := hN
        apply neg_one_pow_congr
        rw [Fin.val_rev]; have := j.isLt; omega
    rw [Even.neg_one_pow (hN.mul_right k), one_smul]
    exact RingHom.congr_fun h f
  · have h : (theta N).comp (longestPerm N) =
        ((longestPerm N).comp (theta N)).comp (parityInv N) :=
      ringHom_ext fun j => by
        simp only [RingHom.comp_apply, longestPerm_generator, theta_generator, map_zsmul,
          parityInv_generator, map_neg]
        rw [← neg_smul]
        congr 1
        obtain ⟨r, hr⟩ := hN
        rw [show -((-1 : ℤ) ^ j.val) = (-1) ^ (j.val + 1) by ring]
        apply neg_one_pow_congr
        rw [Fin.val_rev]; have := j.isLt; omega
    have := RingHom.congr_fun h f
    simp only [RingHom.comp_apply] at this
    rw [this, hf, map_zsmul, map_zsmul, pow_mul, Odd.neg_one_pow hN]

/-- EKL's signed action of the longest element (`x_j ↦ (-1)^{binom(N,2)} x_{N-1-j}`) versus the
plain permutation action: they differ by `(-1)^{binom(N,2) k}` on elements of parity `k`. -/
theorem skewAction_longest (f : SkewPolynomial N) (k : ℕ)
    (hf : parityInv N f = (-1 : ℤ) ^ k • f) :
    SignedPermutation.skewAction (LongestElementary.longest N) f =
      (-1 : ℤ) ^ (N.choose 2 * k) • longestPerm N f := by
  rcases Nat.even_or_odd (N.choose 2) with hN | hN
  · have h : (SignedPermutation.skewAction (LongestElementary.longest N)).toRingHom =
        longestPerm N := ringHom_ext fun j => by
      simp [SignedPermutation.action_generator, LongestElementary.epsilon_longest,
        Even.neg_one_pow hN]
    rw [Even.neg_one_pow (hN.mul_right k), one_smul]
    exact RingHom.congr_fun h f
  · have h : (SignedPermutation.skewAction (LongestElementary.longest N)).toRingHom =
        (longestPerm N).comp (parityInv N) := ringHom_ext fun j => by
      simp [SignedPermutation.action_generator, LongestElementary.epsilon_longest,
        Odd.neg_one_pow hN]
    have := RingHom.congr_fun h f
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply] at this
    rw [this, hf, map_zsmul, pow_mul, Odd.neg_one_pow hN]

theorem parityInv_applyWord {n : ℕ} (f : SkewPolynomial (n+2)) :
    ∀ w : List (Fin (n+1)), parityInv (n+2) (LongestDivided.applyWord w f) =
      (-1 : ℤ) ^ w.length • LongestDivided.applyWord w (parityInv (n+2) f)
  | [] => by simp
  | i :: w => by
    have h : parityInv (n+2) (AllRankDivided.divided i (LongestDivided.applyWord w f)) =
        -AllRankDivided.divided i (parityInv (n+2) (LongestDivided.applyWord w f)) := by
      rw [divided_parityInv, neg_neg]
    rw [LongestDivided.applyWord_cons, LongestDivided.applyWord_cons, h,
      parityInv_applyWord f w, map_zsmul, List.length_cons, pow_succ, mul_neg_one, neg_smul]

/-- `ι ∂_{w_0} = (-1)^{binom(N,2)} ∂_{w_0} ι`. -/
theorem parityInv_D (f : SkewPolynomial N) :
    parityInv N (LongestDivided.D N f) =
      (-1 : ℤ) ^ N.choose 2 • LongestDivided.D N (parityInv N f) := by
  rcases N with _ | _ | n
  · simp [SmallRank.D_small]
  · simp [SmallRank.D_small]
  · rw [LongestDivided.D_eq_inherited, parityInv_applyWord]
    congr 2
    rw [← List.length_map (f := Fin.val), LongestDivided.wordIn_values,
      NilCoxeterWords.coxeterWord_length]

theorem sum_delta (N : ℕ) : ∑ j, delta N j = N.choose 2 := MonomialReversal.sum_rev_val N

/-- `∂_{w_0}(g)` has parity `|a|` for `g = x^δ x^a` or `g = x^a x^δ`. -/
theorem parityInv_D_of (a : Fin N → ℕ) (g : SkewPolynomial N)
    (hg : parityInv N g = (-1 : ℤ) ^ (N.choose 2 + ∑ j, a j) • g) :
    parityInv N (LongestDivided.D N g) = (-1 : ℤ) ^ (∑ j, a j) • LongestDivided.D N g := by
  rw [parityInv_D, hg, map_zsmul, smul_smul, ← pow_add,
    show N.choose 2 + (N.choose 2 + ∑ j, a j) = ∑ j, a j + 2 * N.choose 2 by ring, pow_add,
    pow_mul, neg_one_sq, one_pow, mul_one]

theorem parityInv_staircase_mul (a : Fin N → ℕ) :
    parityInv N (LongestDivided.staircase N * monomial a 1) =
      (-1 : ℤ) ^ (N.choose 2 + ∑ j, a j) • (LongestDivided.staircase N * monomial a 1) := by
  rw [map_mul, staircase_eq_monomial, parityInv_monomial, parityInv_monomial, sum_delta,
    smul_mul_smul_comm, ← pow_add]

theorem parityInv_mul_staircase (a : Fin N → ℕ) :
    parityInv N (monomial a 1 * LongestDivided.staircase N) =
      (-1 : ℤ) ^ (N.choose 2 + ∑ j, a j) • (monomial a 1 * LongestDivided.staircase N) := by
  rw [map_mul, staircase_eq_monomial, parityInv_monomial, parityInv_monomial, sum_delta,
    smul_mul_smul_comm, ← pow_add, add_comm (∑ j, a j)]

/-- `s_a` has parity `|a|`. -/
theorem parityInv_untwisted (a : Fin N → ℕ) :
    parityInv N (untwisted N a) = (-1 : ℤ) ^ (∑ j, a j) • untwisted N a := by
  rw [untwisted, parityInv_longestPerm, parityInv_theta,
    parityInv_D_of a _ (by rw [← map_mul (theta N), parityInv_theta, parityInv_staircase_mul,
      map_zsmul]), map_zsmul, map_zsmul]

/-! ## Twisted versus untwisted odd Schur polynomials -/

theorem crossingCount_add_swap (a b : Fin N → ℕ) :
    OddMath.crossingCount b a + OddMath.crossingCount a b + ∑ j, a j * b j =
      (∑ j, a j) * ∑ j, b j := by
  simp only [OddMath.crossingCount, Finset.sum_filter]
  rw [Finset.sum_comm (f := fun i j => if j < i then b i * a j else 0), Finset.sum_mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : a i * b i = ∑ j, if i = j then a i * b j else 0 := by simp
  rw [e, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, not_lt_of_gt h, mul_comm]
  · simp
  · simp [h, h.ne', not_lt_of_gt h]

theorem weight_delta : ∀ N : ℕ, weight (delta N) = N.choose 3
  | 0 => rfl
  | N + 1 => by
    have ih := weight_delta N
    simp only [weight, delta] at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, mul_zero,
      add_zero]
    have h : ∀ j : Fin N, j.val * (N - j.val) = j.val * (N - 1 - j.val) + j.val := by
      intro j; have := j.isLt
      rw [show N - j.val = (N - 1 - j.val) + 1 by omega, mul_add, mul_one]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, ih, Nat.choose_succ_succ' N 2,
      add_comm (N.choose 3)]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun j => j), Nat.choose_two_right,
      ← Finset.sum_range_id_mul_two, Nat.mul_div_cancel _ two_pos]

theorem sign_identity (a : Fin N → ℕ) :
    (-1 : ℤ) ^ ((N + 1) * ∑ j, a j + (weight (delta N) + weight a)) *
        (OddMath.skewSign (delta N) a * OddMath.skewSign a (delta N)) =
      (-1 : ℤ) ^ (N.choose 3 + N.choose 2 * ∑ j, a j) := by
  rw [OddMath.skewSign, OddMath.skewSign, ← pow_add, ← pow_add]
  have h1 := crossingCount_add_swap a (delta N)
  rw [sum_delta] at h1
  have h2 : (N + 1) * ∑ j, a j + weight a =
      ∑ j, a j * delta N j + 2 * ∑ j, a j * (1 + j.val) := by
    rw [weight, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := j.isLt
    obtain ⟨m, hm⟩ : ∃ m, N = j.val + 1 + m := ⟨N - j.val - 1, by omega⟩
    simp only [delta]
    rw [show N - 1 - j.val = m by omega, show N + 1 = m + j.val + 2 by omega]
    ring
  rw [weight_delta]
  apply neg_one_pow_congr
  have : (N + 1) * ∑ j, a j + (N.choose 3 + weight a) +
      (OddMath.crossingCount (delta N) a + OddMath.crossingCount a (delta N)) =
      N.choose 3 + N.choose 2 * ∑ j, a j + 2 * ∑ j, a j * (1 + j.val) := by
    nlinarith [h1, h2]
  omega

/-- **Ellis–Qi (3.27)**: `s̃_a = θ(s_a)`, for every exponent vector `a`. -/
theorem twisted_eq_theta_untwisted (a : Fin N → ℕ) : twisted N a = theta N (untwisted N a) := by
  have hF : parityInv N (theta N (LongestDivided.D N
      (theta N (LongestDivided.staircase N) * theta N (monomial a 1)))) =
      (-1 : ℤ) ^ (∑ j, a j) • theta N (LongestDivided.D N
        (theta N (LongestDivided.staircase N) * theta N (monomial a 1))) := by
    rw [parityInv_theta, ← map_zsmul]
    congr 1
    exact parityInv_D_of a _ (by rw [← map_mul (theta N), parityInv_theta,
      parityInv_staircase_mul, map_zsmul])
  rw [untwisted, theta_longestPerm _ _ hF, theta_theta, staircase_eq_monomial, theta_monomial,
    theta_monomial, smul_mul_smul_comm, OddSchurPieri.mono_mul, twisted, staircase_eq_monomial,
    OddSchurPieri.mono_mul, add_comm a (delta N)]
  simp only [map_zsmul, smul_smul]
  congr 1
  have h1 := sign_identity a
  have h2 := OddSchurPieri.sign_sq a (delta N)
  simp only [weight] at h1
  linear_combination (-OddMath.skewSign a (delta N)) * h1 +
    ((-1 : ℤ) ^ ((N + 1) * ∑ j, a j) * (-1) ^ (∑ j, j.val * delta N j) *
      (-1) ^ (∑ j, j.val * a j) * OddMath.skewSign (delta N) a) * h2

/-- `s_a = θ(s̃_a)`. -/
theorem untwisted_eq_theta_twisted (a : Fin N → ℕ) : untwisted N a = theta N (twisted N a) := by
  rw [twisted_eq_theta_untwisted, theta_theta]

/-- `s̃_a` has parity `|a|`. -/
theorem parityInv_twisted (a : Fin N → ℕ) :
    parityInv N (twisted N a) = (-1 : ℤ) ^ (∑ j, a j) • twisted N a := by
  rw [twisted_eq_theta_untwisted, parityInv_theta, parityInv_untwisted, map_zsmul]

/-- **Ellis–Qi (3.28)**, the SZ ("Schur through `z`") relations, for the right action
`z f = (θ ∘ w_0)(f) z` of (3.19), Proposition 3.7:
`z s_a = (-1)^{(N+1)|a|} w_0(s̃_a) z`, i.e. `(θ ∘ w_0)(s_a) = (-1)^{(N+1)|a|} w_0(s̃_a)`. -/
theorem sz_relation_left (a : Fin N → ℕ) :
    twistRev N (untwisted N a) = (-1 : ℤ) ^ ((N + 1) * ∑ j, a j) • longestPerm N (twisted N a) := by
  rw [twistRev, RingHom.comp_apply, theta_longestPerm _ _ (parityInv_untwisted a),
    twisted_eq_theta_untwisted]

/-- **Ellis–Qi (3.28)**, second form: `s̃_a z = z w_0(s_a)`, i.e.
`s̃_a = (θ ∘ w_0)(w_0(s_a))`. -/
theorem sz_relation_right (a : Fin N → ℕ) :
    twisted N a = twistRev N (longestPerm N (untwisted N a)) := by
  rw [twistRev, RingHom.comp_apply, longestPerm_longestPerm, twisted_eq_theta_untwisted]

/-! ## Comparison with the odd Schur polynomials of EKL -/

/-- **Ellis–Qi, Remark 3.10**: the twisted odd Schur polynomial is EKL's odd Schur polynomial
(4.17), `s_α = (-1)^{binom(a,3)} (∂_{w_0}(x^α x^δ))^{w_0}` with EKL's signed action of `w_0`. -/
theorem twisted_eq_ekl (n : ℕ) (a : Fin (n+2) → ℕ) : twisted (n+2) a = ThickDots.schur a := by
  rw [twisted, ThickDots.schur, skewAction_longest _ (∑ j, a j)
    (parityInv_D_of a _ (parityInv_mul_staircase a)), smul_smul, ← pow_add]

/-- **Ellis–Qi, Remark 3.10**, every rank: `s̃_a` is EKL's odd Schur polynomial `S(x^a)` of
Definition 2.24 (2.69) (`SmallRank.schurAll`; for partitions of length `≤ n+2` this is
`OddSymmetrizer.schur`). -/
theorem twisted_eq_schurAll (N : ℕ) (a : Fin N → ℕ) : twisted N a = SmallRank.schurAll N a := by
  rcases N with _ | _ | n
  · rw [SmallRank.schurAll_small (by omega), twisted, SmallRank.D_small (by omega),
      SmallRank.staircase_small (by omega), mul_one]
    have : longestPerm 0 (monomial a 1) = monomial a 1 := by
      have h : longestPerm 0 = RingHom.id _ := ringHom_ext fun j => j.elim0
      rw [h, RingHom.id_apply]
    simp [this]
  · rw [SmallRank.schurAll_small (by omega), twisted, SmallRank.D_small (by omega),
      SmallRank.staircase_small (by omega), mul_one]
    have : longestPerm 1 (monomial a 1) = monomial a 1 := by
      have h : longestPerm 1 = RingHom.id _ := ringHom_ext fun j => by
        rw [longestPerm_generator, RingHom.id_apply, Subsingleton.elim j.rev j]
      rw [h, RingHom.id_apply]
    have h3 : Nat.choose 1 3 = 0 := rfl
    simp [this, h3]
  · rw [twisted_eq_ekl]
    rfl

/-! ## Examples in two variables -/

/-- `N = 2`, `λ = (1)`: `d(s_{(1)}) = s_{(2)} + s_{(1,1)}`. -/
theorem d_untwisted_one :
    d 2 (untwisted 2 ![1, 0]) = untwisted 2 ![2, 0] + untwisted 2 ![1, 1] := by
  rw [d_untwisted, Fin.sum_univ_two]
  have e0 : (![1, 0] : Fin 2 → ℕ) + expSingle 0 = ![2, 0] := by
    funext j; fin_cases j <;> rfl
  have e1 : (![1, 0] : Fin 2 → ℕ) + expSingle 1 = ![1, 1] := by
    funext j; fin_cases j <;> rfl
  have c0 : (-1 : ℤ) ^ (rowsAbove ![1, 0] (0 : Fin 2) + (0 : Fin 2).val) *
      (content ![1, 0] 0 % 2) = 1 := by decide
  have c1 : (-1 : ℤ) ^ (rowsAbove ![1, 0] (1 : Fin 2) + (1 : Fin 2).val) *
      (content ![1, 0] 1 % 2) = 1 := by decide
  rw [e0, e1, c0, c1, one_smul, one_smul]

/-- `N = 2`, `λ = (1,1)`: `d(s_{(1,1)}) = s_{(2,1)}` (no box can be added in the second row). -/
theorem d_untwisted_one_one : d 2 (untwisted 2 ![1, 1]) = untwisted 2 ![2, 1] := by
  rw [d_untwisted, Fin.sum_univ_two]
  have e0 : (![1, 1] : Fin 2 → ℕ) + expSingle 0 = ![2, 1] := by
    funext j; fin_cases j <;> rfl
  have e1 : (![1, 1] : Fin 2 → ℕ) + expSingle 1 = ![1, 2] := by
    funext j; fin_cases j <;> rfl
  have c0 : (-1 : ℤ) ^ (rowsAbove ![1, 1] (0 : Fin 2) + (0 : Fin 2).val) *
      (content ![1, 1] 0 % 2) = 1 := by decide
  rw [e0, e1, c0, one_smul, untwisted_eq_zero_of_step (n := 0) ![1, 2] 0 rfl, smul_zero,
    add_zero]

/-- `N = 2`, `λ = (2)`: `d(s_{(2)}) = -s_{(2,1)}` (the box in the first row has content `2`). -/
theorem d_untwisted_two : d 2 (untwisted 2 ![2, 0]) = -untwisted 2 ![2, 1] := by
  rw [d_untwisted, Fin.sum_univ_two]
  have e1 : (![2, 0] : Fin 2 → ℕ) + expSingle 1 = ![2, 1] := by
    funext j; fin_cases j <;> rfl
  have c0 : (-1 : ℤ) ^ (rowsAbove ![2, 0] (0 : Fin 2) + (0 : Fin 2).val) *
      (content ![2, 0] 0 % 2) = 0 := by decide
  have c1 : (-1 : ℤ) ^ (rowsAbove ![2, 0] (1 : Fin 2) + (1 : Fin 2).val) *
      (content ![2, 0] 1 % 2) = -1 := by decide
  rw [e1, c0, c1, zero_smul, zero_add, neg_one_smul]

/-- `N = 2`: `s_{(1)} = x_1 + x_2` (Ellis–Qi's 1-indexed variables), the untwisted `e_1`. -/
theorem untwisted_one_eq : untwisted 2 ![1, 0] = generator 0 + generator 1 := by
  have hm : monomial (![1, 0] : Fin 2 → ℕ) 1 = generator 0 := by
    show monomial _ 1 = monomial (expSingle 0) 1
    congr 1; funext j; fin_cases j <;> rfl
  have hs : LongestDivided.staircase 2 = generator 0 := by
    rw [staircase_eq_monomial]
    show monomial _ 1 = monomial (expSingle 0) 1
    congr 1; funext j; fin_cases j <;> rfl
  have hD : ∀ f, LongestDivided.D 2 f = AllRankDivided.divided (0 : Fin 1) f := fun f => rfl
  rw [untwisted, hm, hs, theta_generator, hD]
  have h0 : (generator (0 : Fin 2) : SkewPolynomial 2) = generator (0 : Fin 1).castSucc := rfl
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [h0, AllRankDivided.divided_left_mul, AllRankDivided.divided_generator]
  simp [sub_eq_add_neg, add_comm]

/-- `N = 2`: `s̃_{(1)} = θ(s_{(1)}) = x_1 - x_2`, the twisted `ẽ_1` (Ellis–Qi §2.4). -/
theorem twisted_one_eq : twisted 2 ![1, 0] = generator 0 - generator 1 := by
  rw [twisted_eq_theta_untwisted, untwisted_one_eq, map_add, theta_generator, theta_generator]
  simp [sub_eq_add_neg]

end

end OddMath.Frontier.EQSchur

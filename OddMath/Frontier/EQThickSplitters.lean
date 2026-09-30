import OddMath.Frontier.EQThickBlocks

/-!
# Ellis–Qi §4.2.1: differentials of splitters and exploders

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §4.1–§4.2.1, Proposition 4.2 and Corollary 4.3.

Ambient ring `ONH_{n+2} = NilHeckeAction.Presented n` with the differential `dONH n`
(`d(x_i) = x_i²`, `d(∂_i) = 1`).  Strands, dots and crossings are `0`-indexed (Ellis–Qi's
`x_{i+1}`), a written product `x * y` is `x` drawn on top of `y`, and `{k} = k mod 2`.

**The differential on thick diagrams.**  A thick diagram with bottom idempotent `e'` and top
idempotent `e` is an element of `e ONH e'`; Ellis–Qi compute its differential by Lemma 2.2,
`d_e(e a e') = e d(a e')`.  Here this is `thickD e y = e * dONH y` (`thickD`), and
`thickD_mul_left` records `e d(e z) = e d(z)` whenever `d(e) ∈ ONH e`.  This is the differential
of the Hom complex, not the restriction of `dONH`: for instance `dONH(∂_{w_0})` contains the extra
terms `Σ {i} x_i ∂_{w_0}` which `e_n` kills.

Conventions (Ellis–Qi §4.1): `e_k = (-1)^{C(k,3)} ∂_{w_0} x^δ` (`eqIdempotent`, and `eqBlock` on
a window of strands);

* the splitter of `a + b` into `a` (left) and `b` (right) is `(e_a ⊗ e_b) e_{a+b}`
  (`splitter`), which equals `e_{a+b}` (`splitter_eq`);
* the merger of `a` and `b` into `a + b` is `e_{a+b} ∂_{a,b} (e_a ⊗ e_b)` (`merger`), with
  `∂_{a,b}` the crossing of the bunch of the `a` left strands at the bottom with the bunch of the
  `b` right strands; we use the reduced expression `crossEQ` obtained by reversing the word of
  `StrandCrossing.crossWord n 0 a b` (EKL (3.41)).  (The printed reduced expression for
  `w_{a,b}` contains index typos; any reduced expression changes `∂_{a,b}`, hence the merger, by
  a global sign, and both sides of Proposition 4.2 are linear in the merger);
* the exploders are `e_n` (thick strand at the bottom) and `∂_{w_0}` (thick strand on top);
* a coupon `ẽ_1` on a thick strand of thickness `k` on the strands `[p, p+k)` is
  `e_k ẽ_1 e_k` with `ẽ_1 = x_p - x_{p+1} + ⋯` (`etBlock`).

Results:

* §4.2.1 display: `e_n d(e_n) = 0` (`eqIdempotent_mul_dONH`) and
  `d(e_n φ e_n) = e_n d(φ) e_n + (-1)^{p(φ)} e_n φ d(e_n)` (`thickD_thick`);
* **Proposition 4.2** (`prop_4_2_splitter`, `prop_4_2_merger`): for `a + b = n + 2`, `b ≥ 1`
  (the printed statement takes `a, b ≥ 1`; `a = 0` is allowed here),
  `d(splitter) = {a} · (splitter with ẽ_1 on the right leg)` and
  `d(merger) = (-1)^{ab-1} {b} · (merger with ẽ_1 on the left leg)`;
* **Corollary 4.3** (`cor_4_3_split`, `cor_4_3_merge`):
  `d(e_n) = Σ_i {i} x_i e_n` and `d(∂_{w_0}) = -(-1)^{C(n,2)} Σ_i {n-1-i} ∂_{w_0} x_i` for the
  differential of Lemma 2.2; `dONH_DElem_ne_thickD_rank_two` shows that the plain `dONH` does not
  satisfy the second formula.

All printed signs hold as stated.  The paper works over a commutative ring `𝕜`; here the
coefficients are `ℤ`.
-/

namespace OddMath.Frontier.EQThick

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis ZeroHecke OnhWindow ThickBubble
open OddMath.Diagrams.OddNilHecke (dONH eqIdempotent parity dONH_mul dot_mem_parity
  crossing_mem_parity one_mem_parity mul_mem_parity dONH_dot_mul dONH_DElem dONH_eqIdempotent)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## The differential of Lemma 2.2 on idempotent-truncated pieces -/

/-- Ellis–Qi Lemma 2.2: the differential on `e ONH e'` is `d_e(y) = e d(y)`. -/
def thickD (e y : Presented n) : Presented n := e * dONH n y

theorem dONH_one : dONH n (1 : Presented n) = 0 := by
  have h := dONH_mul (one_mem_parity n) (1 : Presented n)
  simp only [mul_one, ZMod.val_zero, pow_zero, one_mul] at h
  exact left_eq_add.mp h

/-- For an even idempotent `e`, `e d(e) e = 0`. -/
theorem idem_dONH_idem {e : Presented n} (he : e ∈ parity n 0) (hee : e * e = e) :
    e * dONH n e * e = 0 := by
  have h := dONH_mul he e
  rw [hee, ZMod.val_zero, pow_zero, one_mul] at h
  have hee' : ∀ x, e * (e * x) = e * x := fun x => by rw [← mul_assoc, hee]
  have hX : e * dONH n e * e = e * dONH n e * e + e * dONH n e * e := by
    conv_lhs => rw [h]
    simp only [mul_add, add_mul, mul_assoc, hee, hee']
  exact left_eq_add.mp hX

/-- If `d(e) ∈ ONH e`, then `e d(e) = 0`. -/
theorem idem_dONH_eq_zero {e : Presented n} (he : e ∈ parity n 0) (hee : e * e = e)
    (hd : dONH n e * e = dONH n e) : e * dONH n e = 0 := by
  rw [← hd, ← mul_assoc, idem_dONH_idem he hee]

/-- Lemma 2.2: `d_e(e z) = e d(z)` when `d(e) ∈ ONH e`. -/
theorem thickD_mul_left {e : Presented n} (he : e ∈ parity n 0) (hee : e * e = e)
    (hd : dONH n e * e = dONH n e) (z : Presented n) : thickD e (e * z) = e * dONH n z := by
  rw [thickD, dONH_mul he, ZMod.val_zero, pow_zero, one_mul, mul_add, ← mul_assoc,
    idem_dONH_eq_zero he hee hd, zero_mul, zero_add, ← mul_assoc, hee]

/-! ## Parity and the idempotent `e_n` -/

theorem eqBlock_full (h : 0 + (n + 2) ≤ n + 2) : eqBlock n 0 (n + 2) h = eqIdempotent n := by
  rw [eqBlock_eq h, windowHom_id, RingHom.id_apply]

theorem blockD_full (h : 0 + (n + 2) ≤ n + 2) : blockD n 0 (n + 2) = DElem n := by
  rw [blockD_eq h, windowHom_id, RingHom.id_apply]

theorem eqIdempotent_mem_parity : eqIdempotent n ∈ parity n 0 := by
  rw [← eqBlock_full (by omega)]; exact eqBlock_mem_parity _

theorem DElem_mem_parity : DElem n ∈ parity n ((n + 2).choose 2 : ℕ) := by
  rw [← blockD_full (by omega)]; exact (homog_blockD (by omega)).mem_parity

theorem neg_one_pow_val_natCast (k : ℕ) :
    (-1 : Presented n) ^ ((k : ZMod 2).val) = (-1 : Presented n) ^ k := by
  rw [ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

theorem dONH_eqIdempotent_mul : dONH n (eqIdempotent n) * eqIdempotent n = dONH n (eqIdempotent n) := by
  rw [dONH_eqIdempotent, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, mul_assoc, eqIdempotent_mul_self]

/-- Ellis–Qi §4.2.1: `e_n d(e_n) = 0`. -/
theorem eqIdempotent_mul_dONH : eqIdempotent n * dONH n (eqIdempotent n) = 0 :=
  idem_dONH_eq_zero eqIdempotent_mem_parity (eqIdempotent_mul_self n) dONH_eqIdempotent_mul

/-- Ellis–Qi §4.2.1: on a decorated thick strand,
`d(e_n φ e_n) = e_n d(φ) e_n + (-1)^{p(φ)} e_n φ d(e_n)` for the differential of Lemma 2.2. -/
theorem thickD_thick {k : ZMod 2} {φ : Presented n} (hφ : φ ∈ parity n k) :
    thickD (eqIdempotent n) (eqIdempotent n * φ * eqIdempotent n) =
      eqIdempotent n * dONH n φ * eqIdempotent n +
        (-1 : Presented n) ^ k.val * (eqIdempotent n * φ * dONH n (eqIdempotent n)) := by
  rw [mul_assoc, thickD_mul_left eqIdempotent_mem_parity (eqIdempotent_mul_self n)
    dONH_eqIdempotent_mul, dONH_mul hφ, mul_add, ← mul_assoc (eqIdempotent n) (dONH n φ),
    ((Commute.neg_one_right (eqIdempotent n)).pow_right _).left_comm,
    ← mul_assoc (eqIdempotent n) φ]

/-! ## Corollary 4.3: exploders -/

/-- **Ellis–Qi, Corollary 4.3**, first formula: the exploder `e_n` (thick strand at the bottom,
thin strands on top) has `d(e_n) = Σ_i {i} x_i e_n` (the dot on the `i`-th top strand).  Here the
top idempotent is `1`, so the differential of Lemma 2.2 is `dONH` itself (Lemma 3.5). -/
theorem cor_4_3_split :
    thickD 1 (eqIdempotent n) =
      ∑ i : Fin (n + 2), ((i.val % 2 : ℕ) : Presented n) * (dot n i * eqIdempotent n) := by
  rw [thickD, one_mul, dONH_eqIdempotent]

/-- `{i} e_n x_i ∂_{w_0} = 0` for every `i`. -/
theorem coeff_eqIdempotent_dot_DElem (i : Fin (n + 2)) :
    ((i.val % 2 : ℕ) : Presented n) * (eqIdempotent n * (dot n i * DElem n)) = 0 := by
  rcases Nat.eq_zero_or_pos i.val with h | h
  · rw [h, Nat.zero_mod, Nat.cast_zero, zero_mul]
  · rw [← mul_assoc (eqIdempotent n), eqIdempotent_dot_DElem h, mul_zero]

/-- **Ellis–Qi, Corollary 4.3**, second formula: the exploder `∂_{w_0}` (thin strands at the
bottom, thick strand on top) has
`d(∂_{w_0}) = -(-1)^{C(n,2)} Σ_i {n-1-i} ∂_{w_0} x_i` (the dot on the `i`-th bottom strand), for
the differential `e_n d(-)` of Lemma 2.2 (Lemma 3.4 and `e_n x_i ∂_{w_0} = 0` for `i ≥ 1`). -/
theorem cor_4_3_merge :
    thickD (eqIdempotent n) (DElem n) =
      -((-1 : Presented n) ^ (n + 2).choose 2 *
        ∑ i : Fin (n + 2), (((n + 1 - i.val) % 2 : ℕ) : Presented n) * (DElem n * dot n i)) := by
  have h0 : ∀ i : Fin (n + 2), eqIdempotent n *
      (((i.val % 2 : ℕ) : Presented n) * (dot n i * DElem n)) = 0 := fun i => by
    rw [(Nat.cast_commute _ (eqIdempotent n)).symm.left_comm]
    exact coeff_eqIdempotent_dot_DElem i
  rw [thickD, dONH_DElem, mul_sub, Finset.mul_sum, Finset.sum_eq_zero fun i _ => h0 i, zero_sub,
    ((Commute.neg_one_right (eqIdempotent n)).pow_right _).left_comm, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(Nat.cast_commute _ (eqIdempotent n)).symm.left_comm, ← mul_assoc (eqIdempotent n),
    eqIdempotent_mul_DElem]

/-- The differential of Lemma 2.2 is not the restriction of `dONH`: in rank `2`,
`dONH(∂_{w_0}) = 1`, while `e_2 dONH(∂_{w_0}) = e_2 = ∂_0 x_0 ≠ 1`. -/
theorem dONH_DElem_ne_thickD_rank_two :
    dONH 0 (DElem 0) ≠ thickD (eqIdempotent 0) (DElem 0) := by
  intro h
  have hD : DElem 0 = crossing 0 0 := by
    simp [DElem, LongestDivided.wordIn, LongestDivided.coxeterWord]
  have h1 : dONH 0 (DElem 0) = 1 := by
    rw [hD]; exact OddMath.Diagrams.OddNilHecke.dONH_crossing 0 0
  rw [thickD, h1, mul_one] at h
  have h2 := congrArg (fun z => action 0 z (generator (1 : Fin 2))) h
  rw [map_one (action 0), action_eqIdempotent_generator (by decide)] at h2
  exact Finsupp.single_ne_zero.mpr one_ne_zero h2

/-! ## Proposition 4.2: splitters -/

section Splitter
variable {a b : ℕ}

theorem left_le (hab : a + b = n + 2) : 0 + a ≤ n + 2 := by omega

theorem right_le (hab : a + b = n + 2) : a + b ≤ n + 2 := hab.le

/-- Ellis–Qi §4.1: the splitter of a thick strand `a + b` (bottom) into thick strands `a` (left)
and `b` (right) on top, `(e_a ⊗ e_b) e_{a+b}`. -/
def splitter (n a b : ℕ) (hab : a + b = n + 2) : Presented n :=
  eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) * eqIdempotent n

theorem eqBlock_left_right_comm (hab : a + b = n + 2) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) =
      eqBlock n a b (right_le hab) * eqBlock n 0 a (left_le hab) :=
  homog_comm_of_even (homog_eqBlock _) (homog_eqBlock _) (by omega)
    ((even_two_mul _).mul_right _)

theorem pair_mul_self (hab : a + b = n + 2) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) *
        (eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab)) =
      eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) := by
  rw [mul_assoc, ← mul_assoc (eqBlock n a b _) (eqBlock n 0 a _), ← eqBlock_left_right_comm hab,
    mul_assoc (eqBlock n 0 a _) (eqBlock n a b _), eqBlock_mul_self, ← mul_assoc, eqBlock_mul_self]

theorem pair_mem_parity (hab : a + b = n + 2) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) ∈ parity n 0 := by
  simpa using mul_mem_parity (eqBlock_mem_parity (left_le hab)) (eqBlock_mem_parity (right_le hab))

theorem pair_mul_eqIdempotent (hab : a + b = n + 2) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) * eqIdempotent n =
      eqIdempotent n := by
  rw [mul_assoc, eqBlock_mul_eqIdempotent, eqBlock_mul_eqIdempotent]

/-- As an element of `ONH_{a+b}`, the splitter is `e_{a+b}`. -/
theorem splitter_eq (hab : a + b = n + 2) : splitter n a b hab = eqIdempotent n :=
  pair_mul_eqIdempotent hab

theorem pair_dot_eqIdempotent_left (hab : a + b = n + 2) {i : Fin (n + 2)} (hi1 : 1 ≤ i.val)
    (hia : i.val < a) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) * (dot n i * eqIdempotent n) = 0 := by
  have hc : eqBlock n a b (right_le hab) * dot n i = dot n i * eqBlock n a b (right_le hab) :=
    (homog_comm_of_even (Homog.gen (IsGen.dot i (Nat.zero_le _) hia)) (homog_eqBlock _) le_rfl
      ((even_two_mul _).mul_left _)).symm
  have h1 : eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) * (dot n i * eqIdempotent n) =
      eqBlock n 0 a (left_le hab) * dot n i * eqIdempotent n := by
    rw [mul_assoc, ← mul_assoc (eqBlock n a b _), hc, mul_assoc, eqBlock_mul_eqIdempotent,
      ← mul_assoc]
  rw [h1]
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  have hg := action_eqBlock_generator (left_le hab) i.val hi1 hia
  rw [show (⟨0 + i.val, by omega⟩ : Fin (n + 2)) = i from Fin.ext (Nat.zero_add _)] at hg
  rw [action_mul_apply, action_mul_apply, action_dot_apply,
    NilHeckeRightKernel.action_right_mul n _ _ (action_eqIdempotent_mem f), hg, map_zero,
    LinearMap.zero_apply]
  exact OddMath.SkewPolynomial.zero_mul _

theorem pair_dot_eqIdempotent_right (hab : a + b = n + 2) {i : Fin (n + 2)} (hai : a < i.val) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) * (dot n i * eqIdempotent n) = 0 := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  have hg := action_eqBlock_generator (right_le hab) (i.val - a) (by omega) (by omega)
  rw [show (⟨a + (i.val - a), by omega⟩ : Fin (n + 2)) = i from Fin.ext (by simp; omega)] at hg
  rw [action_mul_apply n _ (dot n i * eqIdempotent n), action_mul_apply n (dot n i),
    action_dot_apply, NilHeckeRightKernel.action_right_mul n _ _ (action_eqIdempotent_mem f),
    action_mul_apply, hg, map_zero, map_zero, LinearMap.zero_apply]
  exact OddMath.SkewPolynomial.zero_mul _

theorem pair_dot_eqIdempotent_self (hab : a + b = n + 2) (hb : 1 ≤ b) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) *
        (dot n ⟨a, by omega⟩ * eqIdempotent n) =
      eqBlock n 0 a (left_le hab) *
          (eqBlock n a b (right_le hab) * etBlock n a b (right_le hab) *
            eqBlock n a b (right_le hab)) * splitter n a b hab := by
  rw [splitter_eq]
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  rw [action_mul_apply _ _ (dot n _ * eqIdempotent n), action_mul_apply _ (dot n _), action_dot_apply,
    NilHeckeRightKernel.action_right_mul n _ _ (action_eqIdempotent_mem f), action_mul_apply,
    action_eqBlock_generator_self (right_le hab) hb, action_mul_apply,
    ← one_mul (action n (eqIdempotent n) f),
    NilHeckeRightKernel.action_right_mul n _ _ (action_eqIdempotent_mem f)]
  simp only [action_mul_apply, action_eqBlock_one]
  rw [action_eqBlock_etBlock, one_mul]

/-- **Ellis–Qi, Proposition 4.2**, first formula: for `a + b = n + 2` and `b ≥ 1` (any `a`),
`d(splitter) = {a} · (splitter with the coupon ẽ_1 on the right leg)`, i.e.
`(e_a ⊗ e_b) d((e_a ⊗ e_b) e_{a+b}) = {a} (e_a ⊗ e_b ẽ_1 e_b) (e_a ⊗ e_b) e_{a+b}`, where
`ẽ_1 = x_a - x_{a+1} + ⋯` on the strands `[a, a+b)` (Ellis–Qi's strands `a+1, …, a+b`) and the
differential is that of Lemma 2.2 with the top idempotent `e_a ⊗ e_b`. -/
theorem prop_4_2_splitter (hab : a + b = n + 2) (hb : 1 ≤ b) :
    thickD (eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab)) (splitter n a b hab) =
      ((a % 2 : ℕ) : Presented n) *
        (eqBlock n 0 a (left_le hab) *
            (eqBlock n a b (right_le hab) * etBlock n a b (right_le hab) *
              eqBlock n a b (right_le hab)) * splitter n a b hab) := by
  set F := eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) with hF
  have h1 : F * (dONH n F * eqIdempotent n) = 0 := by
    rw [← pair_mul_eqIdempotent hab, ← hF, ← mul_assoc, ← mul_assoc,
      idem_dONH_idem (pair_mem_parity hab) (pair_mul_self hab), zero_mul]
  rw [thickD, splitter, ← hF, dONH_mul (pair_mem_parity hab), ZMod.val_zero, pow_zero, one_mul,
    mul_add, h1, zero_add, ← mul_assoc, pair_mul_self hab, dONH_eqIdempotent, Finset.mul_sum,
    Finset.sum_eq_single (⟨a, by omega⟩ : Fin (n + 2))]
  · rw [(Nat.cast_commute _ F).symm.left_comm, pair_dot_eqIdempotent_self hab hb]
    rfl
  · intro i _ hi
    rw [(Nat.cast_commute _ F).symm.left_comm]
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · rw [h0, Nat.zero_mod, Nat.cast_zero, zero_mul]
    · rcases lt_or_gt_of_ne (fun h => hi (Fin.ext h) : i.val ≠ a) with hlt | hgt
      · rw [pair_dot_eqIdempotent_left hab h0 hlt, mul_zero]
      · rw [pair_dot_eqIdempotent_right hab hgt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Splitter

/-! ## Proposition 4.2: mergers -/

section Merger
variable {a b : ℕ}

open NilHeckeRightBasis (reverseLinear reverse_mul reverse_product reverse_one)

/-- Word reversal commutes with shifting windows. -/
theorem reverse_windowHom {m p : ℕ} (h : p + (m + 2) ≤ n + 2) (y : Presented m) :
    reverseLinear n (windowHom m n p h y) = windowHom m n p h (reverseLinear m y) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction c using FreeAlgebra.induction with
  | grade0 r =>
    rw [show Ideal.Quotient.mk (relIdeal m) (algebraMap ℤ (Free m) r) = r • (1 : Presented m) by
      rw [zsmul_eq_mul, mul_one]; simp, map_zsmul, map_zsmul, map_one, reverse_one, map_zsmul,
      reverse_one, map_zsmul, map_one]
  | grade1 g =>
    cases g with
    | inl j =>
      change reverseLinear n (windowHom m n p h (dot m j)) =
        windowHom m n p h (reverseLinear m (dot m j))
      simp
    | inr i =>
      change reverseLinear n (windowHom m n p h (crossing m i)) =
        windowHom m n p h (reverseLinear m (crossing m i))
      simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | mul c d hc hd => rw [map_mul, map_mul, reverse_mul, reverse_mul, map_mul, hc, hd]

theorem reverse_DElem' (m : ℕ) :
    reverseLinear m (DElem m) = (-1 : ℤ) ^ (m + 2).choose 4 • DElem m :=
  OnhReflection.reverse_DElem m

theorem reverse_blockD {p k : ℕ} (h : p + k ≤ n + 2) :
    reverseLinear n (blockD n p k) = (-1 : ℤ) ^ k.choose 4 • blockD n p k := by
  induction k using block_cases with
  | h0 => rw [blockD_zero, reverse_one]; simp
  | h1 => rw [blockD_one, reverse_one]; simp [show Nat.choose 1 4 = 0 by rfl]
  | h2 m => rw [blockD_eq h, reverse_windowHom, reverse_DElem', map_zsmul]

/-- The crossing `∂_{a,b}` of the bunch of the `a` left strands at the bottom with the bunch of the
`b` right strands at the bottom (Ellis–Qi (4.1)), along the reversed word of
`StrandCrossing.crossWord n 0 a b`. -/
def crossEQ (n a b : ℕ) : Presented n := product (StrandCrossing.crossWord n 0 a b).reverse

/-- Ellis–Qi §4.1: the merger of thick strands `a` (left) and `b` (right) at the bottom into a
thick strand `a + b` on top, `e_{a+b} ∂_{a,b} (e_a ⊗ e_b)`. -/
def merger (n a b : ℕ) (hab : a + b = n + 2) : Presented n :=
  eqIdempotent n * crossEQ n a b * (eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab))

/-- `∂_{a,b} (∂_{w_0}' ⊗ ∂_{w_0}'') = θ_{a,b} ∂_{w_0}` for a sign `θ_{a,b}` (Ellis–Qi, proof of
Proposition 4.2). -/
theorem crossEQ_mul_blockD (hab : a + b = n + 2) :
    ∃ θ : ℤ, crossEQ n a b * (blockD n 0 a * blockD n a b) = θ • DElem n := by
  have h := congrArg (reverseLinear n) (blockD_mul_blockD_crossing hab)
  rw [reverse_mul, reverse_mul, reverse_product, reverse_blockD (left_le hab),
    reverse_blockD (right_le hab), reverse_DElem'] at h
  have hc : blockD n 0 a * blockD n a b =
      (-1 : ℤ) ^ (a.choose 2 * b.choose 2) • (blockD n a b * blockD n 0 a) :=
    homog_supercomm_zsmul (homog_blockD (left_le hab)) (homog_blockD (right_le hab)) (by omega)
  set ε : ℤ := (-1 : ℤ) ^ (a.choose 2 * b.choose 2)
  set cL : ℤ := (-1 : ℤ) ^ a.choose 4
  set cR : ℤ := (-1 : ℤ) ^ b.choose 4
  have hε : ε * ε = 1 := neg_one_pow_mul_self _
  have hL : cL * cL = 1 := neg_one_pow_mul_self _
  have hR : cR * cR = 1 := neg_one_pow_mul_self _
  refine ⟨ε * cR * cL * (-1 : ℤ) ^ (n + 2).choose 4, ?_⟩
  rw [smul_mul_smul_comm, mul_smul_comm] at h
  have key : crossEQ n a b * (blockD n a b * blockD n 0 a) =
      (cR * cL * (-1 : ℤ) ^ (n + 2).choose 4) • DElem n := by
    have h2 := congrArg (fun z => (cR * cL) • z) h
    simp only [smul_smul] at h2
    rwa [show cR * cL * (cR * cL) = (cR * cR) * (cL * cL) by ring, hR, hL, one_mul,
      one_smul] at h2
  rw [hc, mul_smul_comm, key, smul_smul]
  congr 1
  ring

/-- The staircase monomial `x^δ = x_p^{k-1} x_{p+1}^{k-2} ⋯ x_{p+k-2}` on the strands `[p, p+k)`. -/
def stairBlock (n p k : ℕ) (h : p + k ≤ n + 2) : Presented n :=
  blockMono n p k h fun i => k - 1 - i.val

theorem eqBlock_eq_stair {p k : ℕ} (h : p + k ≤ n + 2) :
    eqBlock n p k h = (-1 : ℤ) ^ k.choose 3 • (blockD n p k * stairBlock n p k h) := rfl

theorem homog_stairBlock {p k : ℕ} (h : p + k ≤ n + 2) :
    Homog p (p + k) (k.choose 2) (stairBlock n p k h) :=
  homog_of_eq (homog_blockMono h _) (StaircaseValley.sum_staircase k)

/-- `e_a ⊗ e_b = ± (∂_{w_0}' ⊗ ∂_{w_0}'') (x^{δ'} x^{δ''})` (Ellis–Qi, proof of Proposition 4.2). -/
theorem pair_eq (hab : a + b = n + 2) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) =
      ((-1 : ℤ) ^ a.choose 3 * (-1 : ℤ) ^ b.choose 3 * (-1 : ℤ) ^ (a.choose 2 * b.choose 2)) •
        (blockD n 0 a * blockD n a b *
          (stairBlock n 0 a (left_le hab) * stairBlock n a b (right_le hab))) := by
  have hc : stairBlock n 0 a (left_le hab) * blockD n a b =
      (-1 : ℤ) ^ (a.choose 2 * b.choose 2) • (blockD n a b * stairBlock n 0 a (left_le hab)) :=
    homog_supercomm_zsmul (homog_stairBlock _) (homog_blockD (right_le hab)) (by omega)
  rw [eqBlock_eq_stair, eqBlock_eq_stair, smul_mul_smul_comm, mul_assoc (blockD n 0 a),
    ← mul_assoc (stairBlock n 0 a _), hc, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [mul_assoc]

theorem dot_pow_mul_dot {i j : Fin (n + 2)} (h : i ≠ j) (e : ℕ) :
    dot n j ^ e * dot n i = (-1 : ℤ) ^ e • (dot n i * dot n j ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, ZeroHecke.dot_anticommute j i h.symm,
      neg_mul, mul_assoc, ← pow_succ', smul_neg, ← neg_smul, pow_succ]
    congr 1
    ring

/-- `d(x_j^e Y) = {e} x_j^{e+1} Y + (-1)^e x_j^e d(Y)`. -/
theorem dONH_dot_pow_mul (j : Fin (n + 2)) (e : ℕ) (Y : Presented n) :
    dONH n (dot n j ^ e * Y) =
      ((e % 2 : ℕ) : ℤ) • (dot n j ^ (e + 1) * Y) + (-1 : ℤ) ^ e • (dot n j ^ e * dONH n Y) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [show dot n j ^ (e + 1) * Y = dot n j * (dot n j ^ e * Y) by rw [pow_succ', mul_assoc],
      dONH_dot_mul, ih]
    have h1 : dot n j ^ 2 * (dot n j ^ e * Y) = dot n j ^ (e + 1 + 1) * Y := by
      rw [← mul_assoc, ← pow_add, show 2 + e = e + 1 + 1 by omega]
    have h2 : ∀ (c : ℤ) (Z : Presented n) (k : ℕ),
        dot n j * (c • (dot n j ^ k * Z)) = c • (dot n j ^ (k + 1) * Z) := fun c Z k => by
      rw [mul_smul_comm, ← mul_assoc, ← pow_succ']
    have hq : ((((e + 1) % 2 : ℕ)) : ℤ) = 1 - ((e % 2 : ℕ) : ℤ) := by omega
    rw [mul_add, h1, h2, h2, hq, pow_succ (-1 : ℤ) e]
    module

/-- The differential of an ordered product of powers of distinct dots:
`d(x_{j_1}^{e_1} ⋯ x_{j_r}^{e_r}) = Σ_k {e_k} x_{j_k} x_{j_1}^{e_1} ⋯ x_{j_r}^{e_r}`. -/
theorem dONH_dot_list (l : List (Fin (n + 2) × ℕ)) (hl : (l.map Prod.fst).Nodup) :
    dONH n (l.map fun q => dot n q.1 ^ q.2).prod =
      (l.map fun q => ((q.2 % 2 : ℕ) : ℤ) •
        (dot n q.1 * (l.map fun q => dot n q.1 ^ q.2).prod)).sum := by
  induction l with
  | nil => simp [dONH_one]
  | cons q l ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    obtain ⟨hq, hl⟩ := hl
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [dONH_dot_pow_mul, ih hl, pow_succ', mul_assoc]
    congr 1
    rw [← List.sum_map_mul_left, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun q' hq' => ?_
    have hne : q'.1 ≠ q.1 := fun h => hq (h ▸ List.mem_map_of_mem hq')
    simp only [Function.comp_apply]
    rw [mul_smul_comm, ← mul_assoc, dot_pow_mul_dot hne, smul_mul_assoc, smul_comm, smul_smul,
      smul_smul, mul_assoc, neg_one_pow_mul_self, mul_one, mul_assoc]

/-- The exponent list of `x^{δ'} x^{δ''}`. -/
def stairList (n a b : ℕ) (hab : a + b = n + 2) : List (Fin (n + 2) × ℕ) :=
  (List.finRange a).map (fun i => (shiftFin (left_le hab) i, a - 1 - i.val)) ++
    (List.finRange b).map (fun i => (shiftFin (right_le hab) i, b - 1 - i.val))

theorem stair_pair_eq_list (hab : a + b = n + 2) :
    stairBlock n 0 a (left_le hab) * stairBlock n a b (right_le hab) =
      ((stairList n a b hab).map fun q => dot n q.1 ^ q.2).prod := by
  rw [stairBlock, stairBlock, blockMono, blockMono, stairList, List.map_append, List.prod_append,
    List.map_map, List.map_map]
  rfl

theorem stairList_nodup (hab : a + b = n + 2) : ((stairList n a b hab).map Prod.fst).Nodup := by
  rw [stairList, List.map_append, List.map_map, List.map_map]
  refine List.Nodup.append ((List.nodup_finRange a).map fun i j h => ?_)
    ((List.nodup_finRange b).map fun i j h => ?_) ?_
  · simpa [shiftFin, Fin.ext_iff] using h
  · simpa [shiftFin, Fin.ext_iff] using h
  · intro x hx1 hx2
    simp only [List.mem_map, List.mem_finRange, true_and, Function.comp_apply] at hx1 hx2
    obtain ⟨i, rfl⟩ := hx1
    obtain ⟨j, hj⟩ := hx2
    have := congrArg Fin.val hj
    simp only [shiftFin] at this
    have := i.isLt
    omega

/-- `d(x^{δ'} x^{δ''}) = Σ_{i<a} {a-1-i} x_i x^{δ'} x^{δ''} + Σ_{j<b} {b-1-j} x_{a+j} x^{δ'} x^{δ''}`
(Ellis–Qi (3.17) on each block). -/
theorem dONH_stair_pair (hab : a + b = n + 2) :
    dONH n (stairBlock n 0 a (left_le hab) * stairBlock n a b (right_le hab)) =
      ∑ i : Fin a, (((a - 1 - i.val) % 2 : ℕ) : ℤ) • (dot n (shiftFin (left_le hab) i) *
        (stairBlock n 0 a (left_le hab) * stairBlock n a b (right_le hab))) +
      ∑ j : Fin b, (((b - 1 - j.val) % 2 : ℕ) : ℤ) • (dot n (shiftFin (right_le hab) j) *
        (stairBlock n 0 a (left_le hab) * stairBlock n a b (right_le hab))) := by
  rw [stair_pair_eq_list hab, dONH_dot_list _ (stairList_nodup hab), ← stair_pair_eq_list hab,
    stairList,
    List.map_append, List.sum_append, List.map_map, List.map_map, Fin.sum_univ_def,
    Fin.sum_univ_def]
  rfl

/-- The label of Proposition 4.2 slides through the merger:
`(e_a ⊗ e_b) (e_a ẽ_1 e_a ⊗ e_b) = ẽ_1 (e_a ⊗ e_b)` with `ẽ_1` on the left block. -/
theorem pair_label (hab : a + b = n + 2) :
    eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab) *
        (eqBlock n 0 a (left_le hab) * etBlock n 0 a (left_le hab) * eqBlock n 0 a (left_le hab) *
          eqBlock n a b (right_le hab)) =
      etBlock n 0 a (left_le hab) * (eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab)) := by
  set EL := eqBlock n 0 a (left_le hab)
  set ER := eqBlock n a b (right_le hab)
  set T := etBlock n 0 a (left_le hab)
  have hcomm : EL * ER = ER * EL := eqBlock_left_right_comm hab
  have hT : T * ER = ER * T :=
    homog_comm_of_even (homog_etBlock (left_le hab)) (homog_eqBlock (right_le hab)) (by omega)
      ((even_two_mul _).mul_left _)
  have hLL : EL * EL = EL := eqBlock_mul_self _
  have hRR : ER * ER = ER := eqBlock_mul_self _
  have hLTL : EL * T * EL = T * EL := eqBlock_etBlock_eqBlock _
  calc EL * ER * (EL * T * EL * ER) = EL * (ER * EL) * T * EL * ER := by simp only [mul_assoc]
    _ = EL * ER * T * EL * ER := by rw [← hcomm, ← mul_assoc EL EL ER, hLL]
    _ = EL * T * EL * (ER * ER) := by
      rw [mul_assoc EL ER T, ← hT, ← mul_assoc, mul_assoc (EL * T) ER EL, ← hcomm]
      simp only [mul_assoc]
    _ = T * (EL * ER) := by rw [hRR, hLTL, mul_assoc]

theorem etBlock_mul_pair_blockD (hab : a + b = n + 2) :
    etBlock n 0 a (left_le hab) * (blockD n 0 a * blockD n a b) =
      ((-1 : ℤ) ^ (a - 1).choose 2 * (-1 : ℤ) ^ (1 * b.choose 2)) •
        (blockD n 0 a * blockD n a b * etBlock n 0 a (left_le hab)) := by
  have h2 : etBlock n 0 a (left_le hab) * blockD n a b =
      (-1 : ℤ) ^ (1 * b.choose 2) • (blockD n a b * etBlock n 0 a (left_le hab)) :=
    homog_supercomm_zsmul (homog_etBlock _) (homog_blockD (right_le hab)) (by omega)
  rw [← mul_assoc, etBlock_mul_blockD, smul_mul_assoc, mul_assoc, h2, mul_smul_comm, smul_smul,
    ← mul_assoc]

theorem choose_two_add (x y : ℕ) : (x + y).choose 2 = x.choose 2 + y.choose 2 + x * y := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [← add_assoc, Nat.choose_succ_succ, ih, Nat.choose_one_right, Nat.choose_succ_succ,
      Nat.choose_one_right]
    ring

/-- The sign bookkeeping of Proposition 4.2 (merger): for `i < a`,
`(-1)^{C(a+b,2)} ({a-1-i} - {a+b-1-i}) = (-1)^{ab-1} {b} (-1)^{C(a-1,2)} (-1)^{C(b,2)} (-1)^i`. -/
theorem sign_merge (hab : a + b = n + 2) (hb : 1 ≤ b) (i : ℕ) (hi : i < a) :
    (-1 : ℤ) ^ (n + 2).choose 2 * ((((a - 1 - i) % 2 : ℕ) : ℤ) - (((n + 1 - i) % 2 : ℕ) : ℤ)) =
      (-1 : ℤ) ^ (a * b - 1) * ((b % 2 : ℕ) : ℤ) *
        ((-1 : ℤ) ^ (a - 1).choose 2 * (-1 : ℤ) ^ (1 * b.choose 2)) * (-1 : ℤ) ^ i := by
  obtain ⟨u, rfl⟩ : ∃ u, a = u + i + 1 := ⟨a - i - 1, by omega⟩
  rw [← hab, show u + i + 1 - 1 - i = u by omega, show n + 1 - i = u + b by omega,
    show u + i + 1 - 1 = u + i by omega, choose_two_add, show u + i + 1 = (u + i) + 1 by rfl,
    Nat.choose_succ_succ, Nat.choose_one_right, one_mul]
  have hP1 : 1 ≤ (u + i + 1) * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hPm : (u + i + 1) * b % 2 = (u + i + 1) % 2 * (b % 2) % 2 := Nat.mul_mod _ _ _
  generalize (u + i + 1) * b = P at hP1 hPm ⊢
  generalize (u + i).choose 2 = A
  generalize b.choose 2 = B
  have key : ∀ E : ℕ, (-1 : ℤ) ^ E = if E % 2 = 0 then 1 else -1 := by
    intro E; rw [neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one E with h | h <;> simp [h]
  simp only [key]
  rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
  · have : (u + b) % 2 = u % 2 := by omega
    rw [this, hb2]; simp
  · rw [hb2] at hPm ⊢
    split_ifs <;> push_cast <;> omega

/-- Splitting a sum over the strands `[0, a+b)` into the blocks `[0, a)` and `[a, a+b)`. -/
theorem sum_split (hab : a + b = n + 2) {M : Type*} [AddCommMonoid M] (f : Fin (n + 2) → M) :
    ∑ i, f i = ∑ i : Fin a, f (shiftFin (left_le hab) i) +
      ∑ j : Fin b, f (shiftFin (right_le hab) j) := by
  set F : ℕ → M := fun i => if h : i < n + 2 then f ⟨i, h⟩ else 0 with hFdef
  have h1 : ∑ i, f i = ∑ i ∈ Finset.range (n + 2), F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp [F, i.isLt]
  rw [h1, show Finset.range (n + 2) = Finset.range (a + b) by rw [hab], Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range F a, ← Fin.sum_univ_eq_sum_range (fun j => F (a + j)) b]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F]
    rw [dite_eq_left_of_eq_true (eq_true (show i.val < n + 2 by omega))]
    exact congrArg f (Fin.ext (by simp [shiftFin]))
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [F]
    rw [dite_eq_left_of_eq_true (eq_true (show a + j.val < n + 2 by omega))]
    exact congrArg f (Fin.ext (by simp [shiftFin]; omega))

theorem natCast_mul_eq_zsmul (k : ℕ) (y : Presented n) :
    ((k : ℕ) : Presented n) * y = ((k : ℕ) : ℤ) • y := by
  rw [zsmul_eq_mul, Int.cast_natCast]

theorem neg_one_pow_mul_eq_zsmul (k : ℕ) (y : Presented n) :
    (-1 : Presented n) ^ k * y = ((-1 : ℤ) ^ k) • y := by
  rw [zsmul_eq_mul]; push_cast; rfl

/-- **Ellis–Qi, Proposition 4.2**, second formula: for `a + b = n + 2` and `b ≥ 1` (the printed
statement has `a, b ≥ 1`; for `a = 0` both sides vanish, with `ab - 1` truncated in `ℕ`),
`d(merger) = (-1)^{ab-1} {b} · (merger with the coupon ẽ_1 on the left leg)`, i.e.
`e_{a+b} d(e_{a+b} ∂_{a,b} (e_a ⊗ e_b)) =
  (-1)^{ab-1} {b} e_{a+b} ∂_{a,b} (e_a ⊗ e_b) (e_a ẽ_1 e_a ⊗ e_b)`, where
`ẽ_1 = x_0 - x_1 + ⋯` on the strands `[0, a)` and the differential is that of Lemma 2.2 with the
top idempotent `e_{a+b}`. -/
theorem prop_4_2_merger (hab : a + b = n + 2) (hb : 1 ≤ b) :
    thickD (eqIdempotent n) (merger n a b hab) =
      ((-1 : ℤ) ^ (a * b - 1) * ((b % 2 : ℕ) : ℤ)) •
        (merger n a b hab * (eqBlock n 0 a (left_le hab) * etBlock n 0 a (left_le hab) *
          eqBlock n 0 a (left_le hab) * eqBlock n a b (right_le hab))) := by
  obtain ⟨θ, hθ⟩ := crossEQ_mul_blockD hab
  set EL := eqBlock n 0 a (left_le hab) with hEL
  set ER := eqBlock n a b (right_le hab) with hER
  set T := etBlock n 0 a (left_le hab) with hT
  set Δ := stairBlock n 0 a (left_le hab) * stairBlock n a b (right_le hab) with hΔ
  set cF : ℤ := (-1 : ℤ) ^ a.choose 3 * (-1 : ℤ) ^ b.choose 3 *
    (-1 : ℤ) ^ (a.choose 2 * b.choose 2) with hcF
  set s : ℤ := (-1 : ℤ) ^ (a - 1).choose 2 * (-1 : ℤ) ^ (1 * b.choose 2) with hs
  set G : Fin (n + 2) → Presented n := fun i => DElem n * (dot n i * Δ) with hG
  have hpair : EL * ER = cF • (blockD n 0 a * blockD n a b * Δ) := pair_eq hab
  have hM : merger n a b hab = (cF * θ) • (DElem n * Δ) := by
    rw [merger, ← hEL, ← hER, hpair, mul_smul_comm,
      show eqIdempotent n * crossEQ n a b * (blockD n 0 a * blockD n a b * Δ) =
        eqIdempotent n * (crossEQ n a b * (blockD n 0 a * blockD n a b)) * Δ by
          simp only [mul_assoc],
      hθ, mul_smul_comm, smul_mul_assoc, eqIdempotent_mul_DElem, smul_smul]
  have hMY : merger n a b hab * (EL * T * EL * ER) = (cF * s * θ) • (DElem n * (T * Δ)) := by
    rw [merger, ← hEL, ← hER, mul_assoc, pair_label hab, hpair, mul_smul_comm, mul_smul_comm,
      show eqIdempotent n * crossEQ n a b * (T * (blockD n 0 a * blockD n a b * Δ)) =
        eqIdempotent n * crossEQ n a b * (T * (blockD n 0 a * blockD n a b)) * Δ by
          simp only [mul_assoc],
      etBlock_mul_pair_blockD hab, mul_smul_comm, smul_mul_assoc,
      show eqIdempotent n * crossEQ n a b * (blockD n 0 a * blockD n a b * T) * Δ =
        eqIdempotent n * (crossEQ n a b * (blockD n 0 a * blockD n a b)) * (T * Δ) by
          simp only [mul_assoc],
      hθ, mul_smul_comm, smul_mul_assoc, eqIdempotent_mul_DElem, smul_smul, smul_smul]
  have hEd : eqIdempotent n * dONH n (DElem n * Δ) =
      (-1 : ℤ) ^ (n + 2).choose 2 • (DElem n * dONH n Δ) -
        (-1 : ℤ) ^ (n + 2).choose 2 • ∑ i : Fin (n + 2), (((n + 1 - i.val) % 2 : ℕ) : ℤ) • G i := by
    have hc := cor_4_3_merge (n := n)
    rw [thickD] at hc
    rw [dONH_mul DElem_mem_parity, neg_one_pow_val_natCast, mul_add, ← mul_assoc, hc,
      ((Commute.neg_one_right (eqIdempotent n)).pow_right ((n + 2).choose 2)).left_comm,
      ← mul_assoc (eqIdempotent n) (DElem n),
      eqIdempotent_mul_DElem, neg_mul, neg_add_eq_sub, neg_one_pow_mul_eq_zsmul, mul_assoc,
      neg_one_pow_mul_eq_zsmul, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [natCast_mul_eq_zsmul, smul_mul_assoc, mul_assoc]
  have hDT : DElem n * (T * Δ) = ∑ i : Fin a, (-1 : ℤ) ^ i.val • G (shiftFin (left_le hab) i) := by
    rw [hT, etBlock, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
  have hB : ∑ j : Fin b, (((b - 1 - j.val) % 2 : ℕ) : ℤ) • G (shiftFin (right_le hab) j) =
      ∑ j : Fin b, (((n + 1 - (shiftFin (right_le hab) j).val) % 2 : ℕ) : ℤ) •
        G (shiftFin (right_le hab) j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + 1 - (shiftFin (right_le hab) j).val = b - 1 - j.val by simp [shiftFin]; omega]
  rw [thickD, hMY, hM, map_zsmul, mul_smul_comm, hEd, dONH_stair_pair hab, smul_smul,
    sum_split hab, mul_add, Finset.mul_sum, Finset.mul_sum, hDT]
  simp only [mul_smul_comm]
  rw [hB, ← smul_sub, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum,
    Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  have hsi : (shiftFin (left_le hab) i).val = i.val := by simp [shiftFin]
  rw [hsi, mul_assoc (cF * θ), sign_merge hab hb i.val i.isLt, hs]
  ring

end Merger

end

end OddMath.Frontier.EQThick

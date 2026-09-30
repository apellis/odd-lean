import OddMath.Frontier.EQSkewDifferential
import OddMath.Diagrams.OddNilHecke.DifferentialLongestComparison
import OddMath.Frontier.OnhReflection
import OddMath.Frontier.NilHeckeBasis
import OddMath.Frontier.MonomialReversal

/-!
# The odd nilHecke algebra acting on the dg module `Z_n`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.2 (Proposition 3.3, Lemma 3.5, (3.19), Proposition 3.7, Definition 3.8, Corollary 3.9).

On `OPol_n = SkewPolynomial n` (strands numbered from `0`) let `d_z = d_α` for
`α = (0,1,0,1,…)` (`zAlpha`), the differential of the left dg module `Z_n = OPol_n(α)`:
`d_z(f) = d(f) + ι(f) s` with `s = Σ_i {i} x_i`. This file shows that the polynomial action of
`ONH_n` on `Z_n` is compatible with the differentials, which is the content of Corollary 3.9:

* `d_divided_add` : `d ∂_i + ∂_i d = 1 - s_i` on `OPol_n`, where `s_i` is the plain transposition
  (here `ι ∘ s_i^{EKL}`, EKL's signed transposition composed with the parity involution);
* `dZ_divided_add` : `d_z ∂_i + ∂_i d_z = 1` on `Z_n`, i.e. `d(∂_i) = 1` acting on `Z_n`;
* `good_eqIdempotent` : for Ellis–Qi's idempotent `e = (-1)^{binom(n,3)} ∂_{w_0} x^δ`,
  `e` acts by a map commuting with `d_z` up to the parity sign, and with Lemma 3.5 (`d(e) =
  Σ_i {i} x_i e`, `dONH_eqIdempotent`) this gives
* `dZ_D_staircase` (all ranks `N`): for every `g ∈ OPol_N`,
  `d_z(∂_{w_0}(x^δ g)) - ∂_{w_0}(x^δ d_z(g)) = s · ∂_{w_0}(x^δ g)`.

The last identity is the polynomial form of Lemma 3.5 used in the proof of Proposition 3.11.
The auxiliary commutation rules `divided_parityInv` (`∂_i ι = -ι ∂_i`) and
`parityInv_D` (`ι ∂_{w_0} = (-1)^{binom(n,2)} ∂_{w_0} ι`) are also recorded.
-/

namespace OddMath.Frontier.EQSchur

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open EQSkewDifferential AllRankDivided NilHeckeAction
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNUNASemiringSchur (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARingSchur (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- The differential `d_z` of `Z_n = OPol_n(0,1,0,1,…)` (Ellis–Qi Definition 3.8). -/
abbrev dZ (N : ℕ) : SkewPolynomial N →+ SkewPolynomial N := dAlpha (zAlpha N)

/-- `s = Σ_i {i} x_i`, with `{m} = m mod 2` (strands numbered from `0`). -/
abbrev sZ (N : ℕ) : SkewPolynomial N := sAlpha (zAlpha N)

variable {n : ℕ}

/-! ## Divided differences, `ι` and `d` -/

theorem s_s (i : Fin (n+1)) (f : SkewPolynomial (n+2)) : s i (s i f) = f := by
  change SignedPermutation.skewAction _ (SignedPermutation.skewAction _ f) = f
  rw [← SignedPermutation.action_mul, Equiv.swap_mul_self, SignedPermutation.action_one]

theorem parityInv_s (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    parityInv (n+2) (s i f) = s i (parityInv (n+2) f) := by
  have h : (parityInv (n+2)).comp (s i).toRingHom = (s i).toRingHom.comp (parityInv (n+2)) :=
    ringHom_ext fun j => by simp [s_generator]
  exact RingHom.congr_fun h f

/-- `∂_i ι = -ι ∂_i`: the odd divided differences are odd operators. -/
theorem divided_parityInv (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (parityInv (n+2) f) = -parityInv (n+2) (divided i f) := by
  let E : SkewPolynomial (n+2) →+ SkewPolynomial (n+2) :=
    -((parityInv (n+2)).toAddMonoidHom.comp
      ((divided i).toAddMonoidHom.comp (parityInv (n+2)).toAddMonoidHom))
  have hE : ∀ f, E f = -parityInv (n+2) (divided i (parityInv (n+2) f)) := fun f => rfl
  have key := twistedDeriv_ext (s i).toRingHom (D := (divided i).toAddMonoidHom) (E := E)
    (fun f g => divided_mul i f g)
    (fun f g => by
      simp only [hE, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, divided_mul, map_add,
        parityInv_s, parityInv_parityInv, neg_add, mul_neg, neg_mul])
    (fun j => by
      simp only [hE, LinearMap.toAddMonoidHom_coe, parityInv_generator, map_neg,
        divided_generator, neg_neg]
      split_ifs <;> simp)
    (parityInv (n+2) f)
  simp only [LinearMap.toAddMonoidHom_coe, hE, parityInv_parityInv] at key
  exact key

/-- `d s_i = -s_i d` for EKL's signed transposition `s_i`. -/
theorem d_s (i : Fin (n+1)) (f : SkewPolynomial (n+2)) : d (n+2) (s i f) = -s i (d (n+2) f) := by
  let E : SkewPolynomial (n+2) →+ SkewPolynomial (n+2) :=
    -((s i).toAddMonoidHom.comp ((d (n+2)).comp (s i).toAddMonoidHom))
  have hE : ∀ f, E f = -s i (d (n+2) (s i f)) := fun f => rfl
  have key := twistedDeriv_ext (parityInv (n+2)) (D := d (n+2)) (E := E)
    (fun f g => d_mul f g)
    (fun f g => by
      simp only [hE, map_mul, d_mul, map_add, ← parityInv_s, s_s, neg_add, mul_neg, neg_mul])
    (fun j => by
      simp only [hE, s_generator, map_neg, d_generator, neg_mul, mul_neg, neg_neg, map_mul,
        Equiv.swap_apply_self])
    (s i f)
  rw [key, hE, s_s]

theorem sum_mod_two_smul_divided (i : Fin (n+1)) :
    divided i (sZ (n+2)) = 1 := by
  simp only [sZ, sAlpha, zAlpha, map_sum, map_zsmul, divided_generator]
  have hne := adjacent_ne i
  have hsplit : ∀ j : Fin (n+2), (if j = i.castSucc ∨ j = i.succ then (1 : SkewPolynomial (n+2))
      else 0) = (if j = i.castSucc then 1 else 0) + (if j = i.succ then 1 else 0) := by
    intro j
    by_cases h1 : j = i.castSucc
    · have : j ≠ i.succ := h1 ▸ hne
      simp [h1, hne]
    · simp [h1]
  simp only [hsplit, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_castSucc, Fin.val_succ]
  rw [← add_smul]
  have h2 : (((i.val % 2 : ℕ) : ℤ) + (((i.val + 1) % 2 : ℕ) : ℤ)) = 1 := by omega
  rw [h2, one_smul]

private theorem ring_aux {R : Type*} [Ring R] (A M g B C K L L' E H : R) :
    A * g + B * C + (-E * H + K * L) + (M * g + E * H + (-B * C + K * L')) =
      (A + M) * g + K * (L + L') := by
  noncomm_ring

/-- `d ∂_i + ∂_i d = 1 - ι s_i` on `OPol_n`; `ι s_i` is the plain transposition of the variables
`x_i, x_{i+1}`. -/
theorem d_divided_add (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    d (n+2) (divided i f) + divided i (d (n+2) f) = f - parityInv (n+2) (s i f) := by
  let σ : SkewPolynomial (n+2) →+* SkewPolynomial (n+2) := (parityInv (n+2)).comp (s i).toRingHom
  let B : SkewPolynomial (n+2) →+ SkewPolynomial (n+2) :=
    (d (n+2)).comp (divided i).toAddMonoidHom + (divided i).toAddMonoidHom.comp (d (n+2))
  let R : SkewPolynomial (n+2) →+ SkewPolynomial (n+2) :=
    AddMonoidHom.id _ - (parityInv (n+2)).toAddMonoidHom.comp (s i).toAddMonoidHom
  have hB : ∀ f, B f = d (n+2) (divided i f) + divided i (d (n+2) f) := fun f => rfl
  have hR : ∀ f, R f = f - parityInv (n+2) (s i f) := fun f => rfl
  have hσ : ∀ f, σ f = parityInv (n+2) (s i f) := fun f => rfl
  refine twistedDeriv_ext σ (D := B) (E := R) ?_ ?_ ?_ f
  · intro f g
    rw [hB, hB, hB, hσ, divided_mul, map_add, d_mul, d_mul, d_mul, map_add, divided_mul,
      divided_mul, d_s, divided_parityInv, parityInv_s]
    exact ring_aux _ _ _ _ _ _ _ _ _ _
  · intro f g
    rw [hR, hR, hR, hσ, map_mul, map_mul]
    noncomm_ring
  · intro j
    rw [hB, hR]
    simp only [divided_generator, s_generator, map_neg, parityInv_generator, neg_neg]
    have hd0 : ∀ c : Prop, [Decidable c] →
        d (n+2) (if c then (1 : SkewPolynomial (n+2)) else 0) = 0 := by
      intro c _; split_ifs <;> simp
    rw [hd0, zero_add, d_generator, divided_mul, divided_generator, s_generator]
    by_cases h1 : j = i.castSucc
    · subst h1; simp [sub_eq_add_neg]
    · by_cases h2 : j = i.succ
      · subst h2; simp [sub_eq_add_neg]
      · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- `d_z ∂_i + ∂_i d_z = 1` on `Z_n`: the relation `d(∂_i) = 1` of Ellis–Qi Proposition 3.3
holds for the action of `ONH_n` on `Z_n` (Corollary 3.9). -/
theorem dZ_divided_add (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    dZ (n+2) (divided i f) + divided i (dZ (n+2) f) = f := by
  simp only [dZ, dAlpha_apply]
  rw [map_add, divided_mul, sum_mod_two_smul_divided, divided_parityInv, mul_one,
    ← parityInv_s]
  have h := d_divided_add i f
  have e : d (n+2) (divided i f) + parityInv (n+2) (divided i f) * sAlpha (zAlpha (n+2)) +
      (divided i (d (n+2) f) + (-parityInv (n+2) (divided i f) * sAlpha (zAlpha (n+2)) +
        parityInv (n+2) (s i f))) =
      (d (n+2) (divided i f) + divided i (d (n+2) f)) + parityInv (n+2) (s i f) := by
    noncomm_ring
  rw [e, h, sub_add_cancel]

/-! ## Compatibility of the `ONH_n` action with the differentials -/

open OddMath.Diagrams.OddNilHecke (dONH eqIdempotent dONH_dot_mul dONH_crossing_mul
  dONH_eqIdempotent dONH_eq_iff)

/-- `a ∈ ONH_n` of parity `k` acts on `Z_n` compatibly with the differentials:
`(d a) · g = d_z(a · g) - (-1)^k a · d_z(g)`. -/
def Good (a : Presented n) (k : ℕ) : Prop :=
  ∀ g, action n (dONH n a) g = dZ (n+2) (action n a g) - (-1 : ℤ) ^ k • action n a (dZ (n+2) g)

theorem dONH_one : dONH n 1 = 0 := by
  rw [dONH_eq_iff, map_one, map_zero]
  exact OddMath.Diagrams.OddNilHecke.d_one ℤ (n + 2)

theorem good_one : Good (1 : Presented n) 0 := by
  intro g
  rw [dONH_one, map_one, map_zero]
  simp

theorem good_dot_mul {q : Presented n} {k : ℕ} (hq : Good q k) (j : Fin (n+2)) :
    Good (dot n j * q) (k + 1) := by
  intro g
  rw [dONH_dot_mul, sq, map_sub, LinearMap.sub_apply, action_mul_apply, action_mul_apply,
    action_mul_apply, hq, action_mul_apply, action_mul_apply]
  simp only [action_dot_apply, dZ, dAlpha_mul, d_generator, parityInv_generator, mul_sub,
    mul_smul_comm, pow_succ, mul_neg_one, neg_smul, sub_neg_eq_add, neg_mul]
  rw [mul_assoc]
  abel

theorem good_crossing_mul {q : Presented n} {k : ℕ} (hq : Good q k) (i : Fin (n+1)) :
    Good (crossing n i * q) (k + 1) := by
  intro g
  rw [dONH_crossing_mul, map_sub, LinearMap.sub_apply, action_mul_apply, hq, action_mul_apply,
    action_mul_apply, action_crossing_apply, action_crossing_apply, action_crossing_apply, map_sub,
    map_zsmul]
  have h := dZ_divided_add i (action n q g)
  rw [← eq_sub_iff_add_eq] at h
  rw [h, pow_succ, mul_neg_one, neg_smul, sub_neg_eq_add, sub_sub_eq_add_sub, sub_add_eq_add_sub]

theorem good_neg {a : Presented n} {k : ℕ} (ha : Good a k) : Good (-a) k := by
  intro g
  rw [map_neg, map_neg, map_neg, LinearMap.neg_apply, ha, LinearMap.neg_apply,
    LinearMap.neg_apply, map_neg, smul_neg, sub_neg_eq_add, neg_sub, sub_eq_neg_add]

theorem good_product {Y : Presented n} {k : ℕ} (hY : Good Y k) :
    ∀ w : NilCoxeterWords.Word n, Good (NilCoxeterWords.product w * Y) (k + w.length)
  | [] => by simpa [NilCoxeterWords.product] using hY
  | i :: w => by
    rw [NilCoxeterWords.product, mul_assoc, List.length_cons, ← add_assoc]
    exact good_crossing_mul (good_product hY w) i

theorem good_dotPow_mul {Y : Presented n} {k : ℕ} (hY : Good Y k) (j : Fin (n+2)) :
    ∀ a : ℕ, Good (dot n j ^ a * Y) (k + a)
  | 0 => by simpa using hY
  | a + 1 => by
    rw [pow_succ', mul_assoc, ← add_assoc]
    exact good_dot_mul (good_dotPow_mul hY j a) j

theorem good_dotList {Y : Presented n} {k : ℕ} (hY : Good Y k) (A : Fin (n+2) → ℕ) :
    ∀ l : List (Fin (n+2)), Good ((l.map fun i => dot n i ^ A i).prod * Y) (k + (l.map A).sum)
  | [] => by simpa using hY
  | j :: l => by
    rw [List.map_cons, List.prod_cons, mul_assoc, List.map_cons, List.sum_cons,
      show k + (A j + (l.map A).sum) = (k + (l.map A).sum) + A j by ring]
    exact good_dotPow_mul (good_dotList hY A l) j (A j)

theorem sum_staircase_exponent (n : ℕ) :
    ((List.finRange (n+2)).map fun i : Fin (n+2) => n + 1 - i.val).sum = (n+2).choose 2 := by
  rw [← MonomialReversal.sum_rev_val (n+2), Fin.sum_univ_def]
  congr 1

theorem good_eqIdempotent : Good (eqIdempotent n) ((n+2).choose 2 + (n+2).choose 2) := by
  have h1 : Good (NilHeckeBasis.dotMonomial (fun i : Fin (n+2) => n + 1 - i.val) * 1)
      (0 + (n+2).choose 2) := by
    have := good_dotList (good_one (n := n)) (fun i : Fin (n+2) => n + 1 - i.val)
      (List.finRange (n+2))
    rwa [sum_staircase_exponent] at this
  have h2 := good_product h1 (LongestDivided.wordIn n (n+2) le_rfl)
  have hl : (LongestDivided.wordIn n (n+2) le_rfl).length = (n+2).choose 2 := by
    rw [← List.length_map (f := Fin.val), LongestDivided.wordIn_values,
      NilCoxeterWords.coxeterWord_length]
  rw [hl, mul_one, zero_add, ← ZeroHecke.DElem] at h2
  change Good (_ * (ZeroHecke.DElem n * ZeroHecke.staircaseElem n)) _
  rcases neg_one_pow_eq_or (Presented n) ((n+2).choose 3) with h | h
  · rw [h, one_mul]; exact h2
  · rw [h, neg_one_mul]; exact good_neg h2

/-- The action of Ellis–Qi's idempotent: `e · g = (-1)^{binom(n,3)} ∂_{w_0}(x^δ g)`. -/
theorem action_eqIdempotent (g : SkewPolynomial (n+2)) :
    action n (eqIdempotent n) g = (-1 : ℤ) ^ (n+2).choose 3 •
      LongestDivided.D (n+2) (LongestDivided.staircase (n+2) * g) := by
  have hc : ((-1 : Presented n) ^ (n+2).choose 3) = (((-1 : ℤ) ^ (n+2).choose 3 : ℤ) : Presented n) := by
    push_cast; rfl
  rw [eqIdempotent, hc, map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
    action_mul_apply, ZeroHecke.staircaseElem, NilHeckeBasis.action_dotMonomial,
    OnhReflection.action_DElem, OnhReflection.staircase_eq]

/-- **Ellis–Qi, Lemma 3.5 on `Z_n`** (rank `n+2`), polynomial form:
`d_z(∂_{w_0}(x^δ g)) - ∂_{w_0}(x^δ d_z(g)) = s ∂_{w_0}(x^δ g)`, `s = Σ_i {i} x_i`. -/
theorem dZ_D_staircase_add_two (g : SkewPolynomial (n+2)) :
    dZ (n+2) (LongestDivided.D (n+2) (LongestDivided.staircase (n+2) * g)) -
        LongestDivided.D (n+2) (LongestDivided.staircase (n+2) * dZ (n+2) g) =
      sZ (n+2) * LongestDivided.D (n+2) (LongestDivided.staircase (n+2) * g) := by
  have h := good_eqIdempotent (n := n) g
  rw [dONH_eqIdempotent, map_sum, LinearMap.sum_apply] at h
  simp only [map_mul, map_natCast, Module.End.mul_apply, Module.End.natCast_apply,
    action_dot_apply, action_eqIdempotent] at h
  rw [show (-1 : ℤ) ^ ((n+2).choose 2 + (n+2).choose 2) = 1 from
    Even.neg_one_pow ⟨_, rfl⟩, one_smul, map_zsmul, ← smul_sub] at h
  set c : ℤ := (-1 : ℤ) ^ (n+2).choose 3
  have hc : c * c = 1 := by rw [← mul_pow]; norm_num
  have h' := congrArg (fun y => c • y) h
  simp only [smul_smul, hc, one_smul] at h'
  rw [← h']
  simp only [sZ, sAlpha, zAlpha, Finset.sum_mul, Finset.smul_sum, smul_mul_assoc, mul_smul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm c, smul_smul c c, hc, one_smul]
  exact (Nat.cast_smul_eq_nsmul ℤ _ _).symm

end

end OddMath.Frontier.EQSchur

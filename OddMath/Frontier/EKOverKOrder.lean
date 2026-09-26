import OddMath.Frontier.EKOverKChar2
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# EK §2.3 over `k`: the order of ψ₁ and the group `⟨ψ₁, ψ₂⟩`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.3 pp. 19–21: "ψ₁ is not an involution; in
fact it has infinite order", and ψ₁, ψ₂ generate a copy of `ℤ/2 ∗ ℤ/2` (the infinite dihedral
group).  EK state this for an arbitrary commutative ground ring `k` (p. 5).

Main result (`isOfFinOrder_psi1K_iff`): **ψ₁ has finite order on `Λ_k` iff `2` is nilpotent
in `k`.**  Consequently:
* ψ₁ has infinite order over every `k` in which `2` is not nilpotent, e.g. every ring of
  characteristic `0` (`orderOf_psi1K_charZero`) and every field of odd characteristic, in
  particular `𝔽_p` for `p` odd (`orderOf_psi1K_zmod_odd`);
* ψ₁ has order `2` over `𝔽₂` (`F2_orderOf_psi1K`) and finite order over `ℤ/2^e`.

`rhoK : DihedralGroup 0 →* Aut_k(Λ_k)` (`r_i ↦ ψ₁^i`, `sr_i ↦ ψ₂ψ₁^i`) is injective iff `2` is
not nilpotent in `k` (`rhoK_injective_iff`); then `⟨ψ₁, ψ₂⟩ ≅ ℤ/2 ∗ ℤ/2` (`dihedralEquivK`).
Over `𝔽₂`, `⟨ψ₁, ψ₂⟩` has order `2` (`F2_card_closure`).

Proof of infinite order.  A character `χ : Λ_ℤ → ℤ` is determined by `H_χ(t) = Σ χ(h_n) tⁿ`,
and (2.5) gives `Σ_i (-1)^{C(i+1,2)} χ(ψ₁ h_i) χ(h_{n-i}) = δ_{n,0}`.  On the characters with
`χ(h_{2j}) = χ(h_{2j+1}) = g_j` this reads `(1+u) G(-u) G'(u) = 1` for the series `G, G'` of
`χ, χ ∘ ψ₁`.  Starting from `h_1 ↦ 1`, `h_n ↦ 0` (`n ≥ 2`) one gets
`G_{2N} = ((1-u)/(1+u))^N` for `χ ∘ ψ₁^{2N}`.  If `ψ₁^{2N} = 1` on `Λ_k`, then
`(1+u)^N = (1-u)^N` in `k⟦u⟧`, i.e. `2·C(N,j) = 0` in `k` for all odd `j`; by Lucas'
theorem this forces the characteristic of `k` to be a power of `2`.  Conversely
`ψ₁² ≡ 1 mod 2` on `Λ_ℤ`, so `ψ₁^{2^e} ≡ 1 mod 2^e`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ
open EKAutomorphisms (s)
open EKPresentation (psi1)
open EKElementaryQuotient (h e)
open PowerSeries (coeff constantCoeff rescale)

variable {k : Type*} [CommRing k]

/-! ## Powers of ψ₁ on `h₁`, `h₂` -/

theorem psi1K_zpow (i : ℤ) : (psi1K k) ^ i = bcEquiv k (psi1 ^ i) :=
  (bcEquiv_zpow psi1 i).symm

theorem psi1K_pow (n : ℕ) : (psi1K k) ^ n = bcEquiv k (psi1 ^ n) :=
  (bcEquiv_pow psi1 n).symm

theorem psi1K_zpow_h1 (i : ℤ) : ((psi1K k) ^ i) (hK k 1) = hK k 1 := by
  rw [psi1K_zpow, hK, bcEquiv_psiRing, EKInfiniteSymmetry.rotation_h_one]

theorem psi1K_zpow_h2 (i : ℤ) :
    ((psi1K k) ^ i) (hK k 2) = hK k 2 - (i : k) • (hK k 1 * hK k 1) := by
  rw [psi1K_zpow, hK, bcEquiv_psiRing, EKInfiniteSymmetry.rotation_h_two, map_sub,
    psiRing_zsmul, map_mul]
  rfl

theorem psi1K_pow_h2 (n : ℕ) :
    ((psi1K k) ^ n) (hK k 2) = hK k 2 - (n : k) • (hK k 1 * hK k 1) := by
  have := psi1K_zpow_h2 (k := k) n
  rw [zpow_natCast] at this
  simpa using this

/-- Over a ring of characteristic `0`, ψ₁ has infinite order (EK p. 19). -/
theorem orderOf_psi1K_charZero [CharZero k] : orderOf (psi1K k) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn he
  have h := psi1K_pow_h2 (k := k) n
  rw [he, AlgEquiv.one_apply, eq_comm, sub_eq_self, ← hBasisK_yd11] at h
  have := smul_hBasisK_eq_zero h
  exact (Nat.pos_iff_ne_zero.mp hn) (by exact_mod_cast this)

/-! ## Finite order when `2` is nilpotent -/

theorem psi2_mod_two (x : QZ) : ∃ y : QZ, EKAutomorphisms.psi2 x = x + (2 : ℤ) • y := by
  obtain ⟨a, rfl⟩ := EKRadicalQuotient.pi_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨0, ?_⟩
    rw [smul_zero, add_zero, algebraMap_int_eq, eq_intCast, map_intCast, map_intCast]
  | grade1 n =>
    have hn : EKRadicalQuotient.pi (FreeAlgebra.ι ℤ n) = h (n + 1) := rfl
    rw [hn, EKAutomorphisms.psi2_h]
    rcases neg_one_pow_eq_or ℤ ((n + 1 + 1).choose 2) with hs | hs
    · refine ⟨0, ?_⟩
      rw [EKAutomorphisms.s, hs, one_smul, smul_zero, add_zero]
    · refine ⟨-h (n + 1), ?_⟩
      rw [EKAutomorphisms.s, hs, smul_neg, two_smul, neg_one_smul]
      abel
  | mul a b ha hb =>
    obtain ⟨y, hy⟩ := ha
    obtain ⟨y', hy'⟩ := hb
    refine ⟨y * EKRadicalQuotient.pi b + EKRadicalQuotient.pi a * y' + (2 : ℤ) • (y * y'), ?_⟩
    rw [map_mul, map_mul, hy, hy']
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel
  | add a b ha hb =>
    obtain ⟨y, hy⟩ := ha
    obtain ⟨y', hy'⟩ := hb
    refine ⟨y + y', ?_⟩
    rw [map_add, map_add, hy, hy', smul_add]
    abel

theorem psi1_sq_mod_two (x : QZ) : ∃ y : QZ, psi1 (psi1 x) = x + (2 : ℤ) • y := by
  obtain ⟨y1, hy1⟩ := psi2_mod_two (psi1 x)
  obtain ⟨y2, hy2⟩ := psi2_mod_two x
  refine ⟨y2 - psi1 y1, ?_⟩
  have h := EKAutomorphisms.psi1_psi2_psi1 x
  rw [hy1, map_add, map_zsmul, hy2] at h
  rw [smul_sub, ← add_sub_assoc, ← h]
  abel

theorem psi1_pow_mod (r : ℕ) (x : QZ) :
    ∃ y : QZ, (psi1 ^ (2 ^ (r + 1))) x = x + ((2 : ℤ) ^ (r + 1)) • y := by
  induction r generalizing x with
  | zero =>
    obtain ⟨y, hy⟩ := psi1_sq_mod_two x
    exact ⟨y, by simpa [pow_two] using hy⟩
  | succ r ih =>
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨y', hy'⟩ := ih y
    refine ⟨y + (2 : ℤ) ^ r • y', ?_⟩
    have hp : psi1 ^ (2 ^ (r + 1 + 1)) = psi1 ^ (2 ^ (r + 1)) * psi1 ^ (2 ^ (r + 1)) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
    rw [hp, EKInfiniteSymmetry.composition_apply, hy, map_add, map_zsmul, hy, hy', smul_add,
      smul_add, smul_smul, smul_smul]
    have hc1 : (2 : ℤ) ^ (r + 1 + 1) = 2 ^ (r + 1) + 2 ^ (r + 1) := by rw [pow_succ]; ring
    have hc2 : (2 : ℤ) ^ (r + 1 + 1) * 2 ^ r = 2 ^ (r + 1) * 2 ^ (r + 1) := by ring
    rw [hc2, hc1, add_smul]
    abel

/-- If `2` is nilpotent in `k`, then ψ₁ has finite order on `Λ_k`. -/
theorem psi1K_pow_eq_one_of_two_pow {r : ℕ} (hr : (2 : k) ^ (r + 1) = 0) :
    (psi1K k) ^ (2 ^ (r + 1)) = 1 := by
  apply algEquiv_ext
  intro z
  rw [psi1K_pow, bcEquiv_psiRing, AlgEquiv.one_apply]
  obtain ⟨y, hy⟩ := psi1_pow_mod r z
  rw [hy, map_add, psiRing_zsmul]
  push_cast
  rw [hr, zero_smul, add_zero]

theorem isOfFinOrder_psi1K_of_nilpotent (h : IsNilpotent (2 : k)) : IsOfFinOrder (psi1K k) := by
  obtain ⟨r, hr⟩ := h
  have hr' : (2 : k) ^ (r + 1) = 0 := by rw [pow_succ, hr, zero_mul]
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ (r + 1), by positivity,
    psi1K_pow_eq_one_of_two_pow hr'⟩

/-! ## Characters of `Λ_ℤ` of parity type -/

theorem g_hod (G : PowerSeries ℤ) (a b : ℕ) (hab : Even (a + b)) :
    coeff ℤ (a / 2) G * coeff ℤ ((b + 1) / 2) G +
        (-1 : ℤ) ^ a • (coeff ℤ ((b + 1) / 2) G * coeff ℤ (a / 2) G) =
      (-1 : ℤ) ^ a • (coeff ℤ ((a + 1) / 2) G * coeff ℤ (b / 2) G) +
        coeff ℤ (b / 2) G * coeff ℤ ((a + 1) / 2) G := by
  rcases Nat.even_or_odd a with ha | ha
  · have hb : Even b := by
      rcases Nat.even_or_odd b with hb | hb
      · exact hb
      · exact absurd hab (by rw [Nat.not_even_iff_odd]; exact ha.add_odd hb)
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := hb
    have h1 : (d + d + 1) / 2 = (d + d) / 2 := by omega
    have h2 : (c + c + 1) / 2 = (c + c) / 2 := by omega
    rw [h1, h2, Even.neg_one_pow ⟨c, rfl⟩, one_smul, one_smul]
  · rw [Odd.neg_one_pow ha, neg_one_smul, neg_one_smul]
    ring

/-- The character `χ_G : Λ_ℤ → ℤ`, `h_{2j}, h_{2j+1} ↦ [u^j] G` (it respects (2.11)–(2.12)). -/
def chiG (G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1) : QZ →+* ℤ :=
  EKAutomorphisms.descend (fun n => coeff ℤ (n / 2) G) (by simpa using hG)
    (fun a b _ => mul_comm _ _) (g_hod G)

@[simp] theorem chiG_h (G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1) (n : ℕ) :
    chiG G hG (h n) = coeff ℤ (n / 2) G :=
  EKAutomorphisms.descend_h _ _ _ _ n

theorem s_two_mul (l : ℕ) : s (2 * l) = (-1 : ℤ) ^ l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [show 2 * (l + 1) = 2 * l + 2 by ring, EKComplete.s_add_two, ih, pow_succ]; ring

theorem s_two_mul_add_one (l : ℕ) : s (2 * l + 1) = -(-1 : ℤ) ^ l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [show 2 * (l + 1) + 1 = 2 * l + 1 + 2 by ring, EKComplete.s_add_two, ih, pow_succ]; ring

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i = ∑ l ∈ Finset.range m, (f (2 * l) + f (2 * l + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- The parity sum is a coefficient of `(1 - u) A(-u) B(u)`. -/
theorem paritySum_even (A B : PowerSeries ℤ) (j : ℕ) :
    ∑ i ∈ Finset.range (2 * j + 1),
        s i * coeff ℤ (i / 2) A * coeff ℤ ((2 * j - i) / 2) B =
      coeff ℤ j ((1 - PowerSeries.X) * (rescale (-1) A * B)) := by
  rw [Finset.sum_range_succ, sum_range_two_mul, sub_mul, one_mul, map_sub]
  have hc : ∀ n, coeff ℤ n (rescale (-1) A * B) =
      ∑ l ∈ Finset.range (n + 1), (-1 : ℤ) ^ l * coeff ℤ l A * coeff ℤ (n - l) B := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [PowerSeries.coeff_rescale, mul_assoc]
  cases j with
  | zero => simp [hc, EKComplete.s_add_two]
  | succ j =>
    rw [PowerSeries.coeff_succ_X_mul, hc, hc, Finset.sum_range_succ (n := j + 1)]
    simp only [Finset.sum_add_distrib, s_two_mul, s_two_mul_add_one]
    have e1 : ∀ l ∈ Finset.range (j + 1),
        (-1 : ℤ) ^ l * coeff ℤ (2 * l / 2) A * coeff ℤ ((2 * (j + 1) - 2 * l) / 2) B =
          (-1 : ℤ) ^ l * coeff ℤ l A * coeff ℤ (j + 1 - l) B := by
      intro l hl
      have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have a1 : 2 * l / 2 = l := by omega
      have a2 : (2 * (j + 1) - 2 * l) / 2 = j + 1 - l := by omega
      rw [a1, a2]
    have e2 : ∀ l ∈ Finset.range (j + 1),
        -(-1 : ℤ) ^ l * coeff ℤ ((2 * l + 1) / 2) A *
            coeff ℤ ((2 * (j + 1) - (2 * l + 1)) / 2) B =
          -((-1 : ℤ) ^ l * coeff ℤ l A * coeff ℤ (j - l) B) := by
      intro l hl
      have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have a1 : (2 * l + 1) / 2 = l := by omega
      have a2 : (2 * (j + 1) - (2 * l + 1)) / 2 = j - l := by omega
      rw [a1, a2]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib]
    have e3 : (2 * (j + 1)) / 2 = j + 1 := by omega
    have e4 : (2 * (j + 1) - 2 * (j + 1)) / 2 = j + 1 - (j + 1) := by omega
    rw [e3, e4]
    ring

theorem paritySum_odd (A B : PowerSeries ℤ) (j : ℕ) :
    ∑ i ∈ Finset.range (2 * j + 1 + 1),
        s i * coeff ℤ (i / 2) A * coeff ℤ ((2 * j + 1 - i) / 2) B = 0 := by
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, sum_range_two_mul]
  apply Finset.sum_eq_zero
  intro l hl
  have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [s_two_mul, s_two_mul_add_one]
  have e1 : 2 * l / 2 = l := by omega
  have e2 : (2 * l + 1) / 2 = l := by omega
  have e3 : (2 * j + 1 - 2 * l) / 2 = j - l := by omega
  have e4 : (2 * j + 1 - (2 * l + 1)) / 2 = j - l := by omega
  rw [e1, e2, e3, e4]
  ring

theorem rescale_one_add_X : rescale (-1 : ℤ) (1 + PowerSeries.X) = 1 - PowerSeries.X := by
  rw [map_add, map_one, PowerSeries.rescale_neg_one_X, sub_eq_add_neg]

theorem rescale_rescale_neg_one (G : PowerSeries ℤ) : rescale (-1 : ℤ) (rescale (-1) G) = G := by
  rw [PowerSeries.rescale_rescale, neg_one_mul, neg_neg, PowerSeries.rescale_one]; rfl

/-- The relation (2.5), evaluated by a character. -/
theorem character_relation (χ : QZ →+* ℤ) (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.range (n + 1), s i * χ (e i) * χ (h (n - i)) = 0 := by
  have := congrArg χ (EKComplete.relation_2_5 n hn)
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_mul, smul_eq_mul, mul_assoc]

/-- **The step `χ ↦ χ ∘ ψ₁` on parity characters:** if `(1+u) G(-u) G'(u) = 1`, then
`χ_G ∘ ψ₁ = χ_{G'}`. -/
theorem chiG_comp_psi1 (G G' : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1)
    (hG' : constantCoeff ℤ G' = 1)
    (hrel : (1 + PowerSeries.X) * rescale (-1) G * G' = 1) :
    (chiG G hG).comp psi1.toRingHom = chiG G' hG' := by
  apply EKAutomorphisms.hom_ext_h
  intro n
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    EKPresentation.psi1_h, chiG_h]
  -- the defining relation of `G'`, coefficientwise
  have hrel' : (1 - PowerSeries.X) * (rescale (-1) G' * G) = 1 := by
    have := congrArg (rescale (-1 : ℤ)) hrel
    rw [map_mul, map_mul, rescale_one_add_X, rescale_rescale_neg_one, map_one] at this
    linear_combination this
  have key' : ∀ m, 0 < m →
      ∑ i ∈ Finset.range (m + 1), s i * coeff ℤ (i / 2) G' * coeff ℤ ((m - i) / 2) G = 0 := by
    intro m hm
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [paritySum_even, hrel', PowerSeries.coeff_one, if_neg (by omega)]
    · exact paritySum_odd G' G j
  have keyd : ∀ m, 0 < m →
      ∑ i ∈ Finset.range (m + 1), s i * chiG G hG (e i) * coeff ℤ ((m - i) / 2) G = 0 := by
    intro m hm
    have := character_relation (chiG G hG) m hm
    simpa only [chiG_h] using this
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [e, CompleteElementary.elementary_zero, map_one, map_one]
      simpa using hG'.symm
    · have h1 := keyd n hn
      have h2 := key' n hn
      rw [Finset.sum_range_succ] at h1 h2
      have hsum : ∑ i ∈ Finset.range n, s i * chiG G hG (e i) * coeff ℤ ((n - i) / 2) G =
          ∑ i ∈ Finset.range n, s i * coeff ℤ (i / 2) G' * coeff ℤ ((n - i) / 2) G := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ih i (Finset.mem_range.mp hi)]
      rw [hsum, Nat.sub_self, Nat.zero_div] at h1
      rw [Nat.sub_self, Nat.zero_div] at h2
      have hc : coeff ℤ 0 G = 1 := by simpa using hG
      rw [hc, mul_one] at h1 h2
      have h3 : s n * chiG G hG (e n) = s n * coeff ℤ (n / 2) G' := by linarith
      exact mul_left_cancel₀ (EKComplete.s_ne_zero n) h3

/-! ## The orbit of the character `h₁ ↦ 1`, `h_n ↦ 0` (`n ≥ 2`) -/

theorem constantCoeff_step (G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1) :
    constantCoeff ℤ ((1 + PowerSeries.X) * rescale (-1) G) = ((1 : ℤˣ) : ℤ) := by
  rw [map_mul, map_add, map_one, PowerSeries.constantCoeff_X, add_zero, one_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, Units.val_one]

/-- The series `G_m` of `χ₁ ∘ ψ₁^m`, and `constantCoeff G_m = 1`. -/
def Gs : ℕ → {G : PowerSeries ℤ // constantCoeff ℤ G = 1}
  | 0 => ⟨1, map_one _⟩
  | m + 1 => ⟨PowerSeries.invOfUnit ((1 + PowerSeries.X) * rescale (-1) (Gs m).1) 1, by
      rw [PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]⟩

theorem Gs_rel (m : ℕ) : (1 + PowerSeries.X) * rescale (-1) (Gs m).1 * (Gs (m + 1)).1 = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (constantCoeff_step _ (Gs m).2)

/-- The character `χ₁ : h₁ ↦ 1`, `h_n ↦ 0` for `n ≥ 2`. -/
def chi1 : QZ →+* ℤ := chiG 1 (map_one _)

theorem chi1_pow (m : ℕ) (x : QZ) : chi1 ((psi1 ^ m) x) = chiG (Gs m).1 (Gs m).2 x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, EKInfiniteSymmetry.composition_apply, ih]
    exact RingHom.congr_fun (chiG_comp_psi1 _ _ (Gs m).2 (Gs (m + 1)).2 (Gs_rel m)) x

theorem Gs_closed (N : ℕ) :
    (Gs (2 * N)).1 * (1 + PowerSeries.X) ^ N = (1 - PowerSeries.X) ^ N ∧
      (Gs (2 * N + 1)).1 * (1 + PowerSeries.X) ^ (N + 1) = (1 - PowerSeries.X) ^ N := by
  have odd_of_even : ∀ N, (Gs (2 * N)).1 * (1 + PowerSeries.X) ^ N = (1 - PowerSeries.X) ^ N →
      (Gs (2 * N + 1)).1 * (1 + PowerSeries.X) ^ (N + 1) = (1 - PowerSeries.X) ^ N := by
    intro N hN
    have h1 := congrArg (rescale (-1 : ℤ)) hN
    rw [map_mul, map_pow, map_pow, rescale_one_add_X, map_sub, map_one,
      PowerSeries.rescale_neg_one_X, sub_neg_eq_add] at h1
    have h2 := Gs_rel (2 * N)
    linear_combination (-((Gs (2 * N + 1)).1 * (1 + PowerSeries.X))) * h1 +
      (1 - PowerSeries.X) ^ N * h2
  induction N with
  | zero => exact ⟨by simp [Gs], odd_of_even 0 (by simp [Gs])⟩
  | succ N ih =>
    have hE : (Gs (2 * (N + 1))).1 * (1 + PowerSeries.X) ^ (N + 1) =
        (1 - PowerSeries.X) ^ (N + 1) := by
      have h1 := congrArg (rescale (-1 : ℤ)) ih.2
      rw [map_mul, map_pow, map_pow, rescale_one_add_X, map_sub, map_one,
        PowerSeries.rescale_neg_one_X, sub_neg_eq_add] at h1
      have h2 := Gs_rel (2 * N + 1)
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
      linear_combination (-((Gs (2 * N + 1 + 1)).1 * (1 + PowerSeries.X))) * h1 +
        (1 - PowerSeries.X) ^ (N + 1) * h2
    exact ⟨hE, odd_of_even (N + 1) hE⟩

/-! ## Infinite order when `2` is not nilpotent -/

theorem coeff_one_add_X_pow' {R : Type*} [CommRing R] (N j : ℕ) :
    coeff R j ((1 + PowerSeries.X) ^ N) = (N.choose j : R) := by
  have : ((1 + PowerSeries.X) ^ N : PowerSeries R) = (((1 + Polynomial.X) ^ N : Polynomial R) :
      PowerSeries R) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem coeff_one_sub_X_pow' {R : Type*} [CommRing R] (N j : ℕ) :
    coeff R j ((1 - PowerSeries.X) ^ N) = (-1 : R) ^ j * (N.choose j : R) := by
  have : ((1 - PowerSeries.X) ^ N : PowerSeries R) = rescale (-1 : R) ((1 + PowerSeries.X) ^ N) := by
    rw [map_pow, map_add, map_one, PowerSeries.rescale_neg_one_X, sub_eq_add_neg]
  rw [this, PowerSeries.coeff_rescale, coeff_one_add_X_pow']

/-- If `ψ₁^{2N} = 1` on `Λ_k` (`N ≥ 1`), then `2·C(N,j) = 0` in `k` for every odd `j`. -/
theorem two_choose_eq_zero_of_pow {N : ℕ} (hN : (psi1K k) ^ (2 * N) = 1) (j : ℕ) (hj : Odd j) :
    ((2 * N.choose j : ℕ) : k) = 0 := by
  have hcoef : ∀ i, ((coeff ℤ i (Gs (2 * N)).1 : ℤ) : k) = ((coeff ℤ i (1 : PowerSeries ℤ) : ℤ) : k) := by
    intro i
    have := congrArg (bcChar k chi1) (congrArg (fun f : LamK k ≃ₐ[k] LamK k => f (hK k (2 * i))) hN)
    simp only [AlgEquiv.one_apply] at this
    rw [psi1K_pow, hK, bcEquiv_psiRing, bcChar_psiRing, bcChar_psiRing, chi1_pow, chiG_h] at this
    rw [chi1, chiG_h] at this
    simpa [Nat.mul_div_cancel_left i two_pos] using this
  have hmap : PowerSeries.map (Int.castRingHom k) (Gs (2 * N)).1 = 1 := by
    ext i
    rw [PowerSeries.coeff_map, eq_intCast, hcoef i, PowerSeries.coeff_one,
      PowerSeries.coeff_one]
    split_ifs <;> simp
  have h := congrArg (PowerSeries.map (Int.castRingHom k)) (Gs_closed N).1
  rw [map_mul, hmap, one_mul, map_pow, map_pow, map_add, map_sub, map_one,
    PowerSeries.map_X] at h
  have hc := congrArg (coeff k j) h
  rw [coeff_one_add_X_pow', coeff_one_sub_X_pow', Odd.neg_one_pow hj] at hc
  push_cast
  linear_combination hc

/-- Lucas: `C(q^v m, q^v) ≡ m (mod q)`. -/
theorem choose_prime_pow_mul (q : ℕ) [Fact q.Prime] (v m : ℕ) :
    (q ^ v * m).choose (q ^ v) ≡ m [MOD q] := by
  induction v with
  | zero => simpa using Nat.ModEq.refl m
  | succ v ih =>
    have hq : 0 < q := (Fact.out : q.Prime).pos
    refine (Choose.choose_modEq_choose_mod_mul_choose_div_nat).trans ?_
    have h1 : q ^ (v + 1) * m % q = 0 := by
      rw [pow_succ, mul_assoc, mul_comm q, ← mul_assoc]; exact Nat.mul_mod_left _ _
    have h2 : q ^ (v + 1) % q = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
    have h3 : q ^ (v + 1) * m / q = q ^ v * m := by
      rw [pow_succ, mul_assoc, mul_comm q, ← mul_assoc]; exact Nat.mul_div_cancel _ hq
    have h4 : q ^ (v + 1) / q = q ^ v := by rw [pow_succ]; exact Nat.mul_div_cancel _ hq
    rw [h1, h2, h3, h4, Nat.choose_self, one_mul]
    exact ih

/-- For an odd prime `q` and `N ≥ 1` some `C(N, j)`, `j` odd, is prime to `q`. -/
theorem exists_odd_choose_not_dvd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {N : ℕ} (hN : 0 < N) :
    ∃ j, Odd j ∧ ¬ q ∣ N.choose j := by
  haveI := Fact.mk hq
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.one_lt.ne'
  refine ⟨q ^ v, (hq.odd_of_ne_two hq2).pow, fun hd => hm ?_⟩
  have := (choose_prime_pow_mul q v m).symm
  exact (Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr hd)))

/-- If `2·C(N,j) = 0` in `k` for all odd `j` (some `N ≥ 1`), then `2` is nilpotent in `k`. -/
theorem isNilpotent_two_of_choose {N : ℕ} (hN : 0 < N)
    (h : ∀ j, Odd j → ((2 * N.choose j : ℕ) : k) = 0) : IsNilpotent (2 : k) := by
  set p := ringChar k with hp
  have hdvd : ∀ j, Odd j → p ∣ 2 * N.choose j := fun j hj =>
    (ringChar.spec k _).mp (h j hj)
  have hp0 : p ≠ 0 := by
    intro h0
    have := hdvd 1 odd_one
    rw [h0, Nat.choose_one_right, zero_dvd_iff] at this
    omega
  have hpow : p = 2 ^ p.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hp0
    intro d hd hdp
    by_contra hd2
    obtain ⟨j, hj, hnd⟩ := exists_odd_choose_not_dvd hd hd2 hN
    have := (hd.dvd_mul.mp (hdp.trans (hdvd j hj)))
    rcases this with h2 | h2
    · exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)
    · exact hnd h2
  refine ⟨p.primeFactorsList.length, ?_⟩
  have := ringChar.Nat.cast_ringChar (R := k)
  rw [← hp, hpow] at this
  exact_mod_cast this

/-- If ψ₁ has finite order on `Λ_k`, then `2` is nilpotent in `k`. -/
theorem nilpotent_of_isOfFinOrder (h : IsOfFinOrder (psi1K k)) : IsNilpotent (2 : k) := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  have h2 : (psi1K k) ^ (2 * n) = 1 := by rw [mul_comm, pow_mul, hpow, one_pow]
  exact isNilpotent_two_of_choose hn (two_choose_eq_zero_of_pow h2)

/-- **EK p. 19 over `k`, exact form: ψ₁ has finite order on `Λ_k` iff `2` is nilpotent in
`k`.**  So "ψ₁ has infinite order" holds exactly when `2` is not nilpotent in `k`. -/
theorem isOfFinOrder_psi1K_iff : IsOfFinOrder (psi1K k) ↔ IsNilpotent (2 : k) :=
  ⟨nilpotent_of_isOfFinOrder, isOfFinOrder_psi1K_of_nilpotent⟩

theorem orderOf_psi1K_eq_zero_iff : orderOf (psi1K k) = 0 ↔ ¬ IsNilpotent (2 : k) := by
  rw [orderOf_eq_zero_iff, isOfFinOrder_psi1K_iff]

/-- Over `𝔽_p`, `p` an odd prime, ψ₁ has infinite order. -/
theorem orderOf_psi1K_zmod_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    orderOf (psi1K (ZMod p)) = 0 := by
  rw [orderOf_psi1K_eq_zero_iff]
  intro hn
  have h0 : (2 : ZMod p) = 0 := hn.eq_zero
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at this
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

/-- Over `𝔽₂`, ψ₁ has order `2`. -/
theorem F2_orderOf_psi1K : orderOf (psi1K (ZMod 2)) = 2 := by
  apply orderOf_eq_prime
  · apply algEquiv_ext
    intro z
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact F2_psi1K_involutive _
  · intro h1
    have := psi1K_pow_h2 (k := ZMod 2) 1
    rw [pow_one, h1, AlgEquiv.one_apply, Nat.cast_one, one_smul, eq_comm, sub_eq_self,
      ← hBasisK_yd11] at this
    have h := congrArg (fun x => (hBasisK (k := ZMod 2)).repr x yd11) this
    simp only [Basis.repr_self, Finsupp.single_eq_same, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h
    exact one_ne_zero h

/-! ## The group `⟨ψ₁, ψ₂⟩` -/

variable (k) in
/-- `DihedralGroup 0 → Aut_k(Λ_k)`, `r_i ↦ ψ₁^i`, `sr_i ↦ ψ₂ψ₁^i`. -/
def rhoK : DihedralGroup 0 →* (LamK k ≃ₐ[k] LamK k) := (bcHom k).comp EKInfiniteSymmetry.rho

@[simp] theorem rhoK_r (i : ℤ) : rhoK k (.r i) = (psi1K k) ^ i := by
  simp [rhoK, psi1K, bcEquiv_zpow]

@[simp] theorem rhoK_sr (i : ℤ) : rhoK k (.sr i) = psi2K k * (psi1K k) ^ i := by
  simp [rhoK, psi1K, psi2K, bcEquiv_zpow, map_mul]

theorem psi2K_h1 : psi2K k (hK k 1) = -hK k 1 := by
  rw [psi2K_h]; simp [s]

theorem rotation_ne_reflectionK (h2 : (2 : k) ≠ 0) (i j : ℤ) :
    (psi1K k) ^ i ≠ psi2K k * (psi1K k) ^ j := by
  intro he
  have := congrArg (fun f : LamK k ≃ₐ[k] LamK k => f (hK k 1)) he
  simp only [AlgEquiv.mul_apply, psi1K_zpow_h1, psi2K_h1] at this
  rw [eq_neg_iff_add_eq_zero, ← two_smul k] at this
  apply h2
  apply smul_hBasisK_eq_zero (μ := yd [1] (by decide))
  rw [hBasisK_yd _ _ (by decide)]
  simpa using this

/-- **EK p. 20 over `k`:** `r_i ↦ ψ₁^i`, `sr_i ↦ ψ₂ψ₁^i` is injective on the infinite
dihedral group `ℤ/2 ∗ ℤ/2` iff `2` is not nilpotent in `k`. -/
theorem rhoK_injective_iff : Function.Injective (rhoK k) ↔ ¬ IsNilpotent (2 : k) := by
  constructor
  · intro hinj hn
    obtain ⟨n, hn0, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_psi1K_of_nilpotent hn)
    have : rhoK k (.r (n : ℤ)) = rhoK k (.r 0) := by
      rw [rhoK_r, rhoK_r, zpow_natCast, hpow, zpow_zero]
    have := hinj this
    simp only [DihedralGroup.r.injEq, Nat.cast_eq_zero] at this
    omega
  · intro hn
    have hinf : Function.Injective fun i : ℤ => (psi1K k) ^ i :=
      injective_zpow_iff_not_isOfFinOrder.mpr (fun h => hn (nilpotent_of_isOfFinOrder h))
    have h2 : (2 : k) ≠ 0 := fun h0 => hn ⟨1, by rw [pow_one, h0]⟩
    rintro (i | i) (j | j) he
    · simp only [rhoK_r] at he; exact congrArg DihedralGroup.r (hinf he)
    · simp only [rhoK_r, rhoK_sr] at he; exact (rotation_ne_reflectionK h2 i j he).elim
    · simp only [rhoK_r, rhoK_sr] at he; exact (rotation_ne_reflectionK h2 j i he.symm).elim
    · simp only [rhoK_sr] at he; exact congrArg DihedralGroup.sr (hinf (mul_left_cancel he))

theorem range_rhoK : (rhoK k).range = Subgroup.closure {psi1K k, psi2K k} := by
  rw [rhoK, MonoidHom.range_comp, EKInfiniteSymmetry.range_eq_generated,
    EKInfiniteSymmetry.generated, MonoidHom.map_closure, Set.image_pair]
  rfl

/-- **EK p. 20 over `k`:** if `2` is not nilpotent in `k` (e.g. `k` of characteristic `0` or a
field of odd characteristic), then `⟨ψ₁, ψ₂⟩ ≅ ℤ/2 ∗ ℤ/2`, the infinite dihedral group. -/
def dihedralEquivK (hn : ¬ IsNilpotent (2 : k)) :
    DihedralGroup 0 ≃* Subgroup.closure ({psi1K k, psi2K k} : Set (LamK k ≃ₐ[k] LamK k)) :=
  (MonoidHom.ofInjective ((rhoK_injective_iff (k := k)).mpr hn)).trans
    (MulEquiv.subgroupCongr range_rhoK)

@[simp] theorem dihedralEquivK_apply (hn : ¬ IsNilpotent (2 : k)) (g : DihedralGroup 0) :
    ((dihedralEquivK hn g : _) : LamK k ≃ₐ[k] LamK k) = rhoK k g := rfl

/-- Over `𝔽₂`, `⟨ψ₁, ψ₂⟩ = ⟨ψ₁⟩` has order `2` (not `ℤ/2 ∗ ℤ/2`). -/
theorem F2_closure_eq :
    Subgroup.closure ({psi1K (ZMod 2), psi2K (ZMod 2)} : Set (LamK (ZMod 2) ≃ₐ[ZMod 2] _)) =
      Subgroup.zpowers (psi1K (ZMod 2)) := by
  rw [F2_psi2K, Subgroup.zpowers_eq_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro f (rfl | rfl)
    · exact Subgroup.subset_closure rfl
    · exact Subgroup.one_mem _
  · exact Subgroup.closure_mono (by simp)

theorem F2_card_closure :
    Nat.card (Subgroup.closure
      ({psi1K (ZMod 2), psi2K (ZMod 2)} : Set (LamK (ZMod 2) ≃ₐ[ZMod 2] _))) = 2 := by
  rw [F2_closure_eq, Nat.card_zpowers, F2_orderOf_psi1K]

theorem F2_rhoK_not_injective : ¬ Function.Injective (rhoK (ZMod 2)) := by
  rw [rhoK_injective_iff, not_not]
  exact ⟨1, by rw [pow_one]; exact two_eq_zero_F2⟩

end OddMath.Frontier.EKOverK

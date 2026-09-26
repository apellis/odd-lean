import OddMath.Frontier.EKCenterPower
import OddMath.Frontier.EKCenterPowerControls
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! # Algebraic independence of the even odd power sums `p_{2k}`

EK arXiv:1107.5610v2, §3.2, p. 26: "the center … is precisely the polynomial algebra generated
by the `p_{2k}`'s". This file proves the independence half, integrally at q = -1 in the
radical quotient `Q`, with `p_n = m_n = EKCenterPower.p n`.

* `pairing_p_mul`: for `a ≥ 1` and any `Y`,
  `(p_{2a} Y, h_β) = Σ_{j : 2a ≤ β_j} (Y, h_{β - 2a e_j})` (primitivity of `p_{2a}` in the form
  `(x, p_{2a}) = snd ψ(x)`, `EKCenterPower.phi_pi`, plus adjointness).
* `pP λ = p_{2λ₁} ⋯ p_{2λ_r}`; `pP_linearIndependent`: the family `(pP λ)_λ`, `λ` over all
  partitions, is ℤ-linearly independent. Test elements are `h_{2μ}`: `(pP λ, h_{2μ}) ≠ 0` forces
  `ℓ(μ) ≤ ℓ(λ)`, with `μ = λ` in case of equality, and `(pP λ, h_{2λ}) > 0`.
* `algebraicIndependent_p`: the `p_{2k}`, `k ≥ 1`, viewed in the (commutative) centre of `Q`,
  are algebraically independent over `ℤ`.
-/

noncomputable section
open scoped BigOperators DualNumber

namespace OddMath.Frontier.EKRest
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient EKPairingMatrices
open EKCenterPower (p psi psi_h phi_pi pairing_lift)

/-- `h_β` for a tuple `β` (zero parts are `h₀ = 1`). -/
def hw {r : ℕ} (β : Fin r → ℕ) : Q := pi (EKMixedPairing.word β (fun _ => false))

theorem psi_prod {r : ℕ} (k : ℕ) (hk : 0 < k) (γ : Fin r → ℕ) :
    (∏ i, psi k (CompleteElementary.h (γ i))) =
      if (∀ i, γ i = 0) then 1 else if (∃ j, γ = Pi.single j k) then DualNumber.eps else 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.prod_univ_succ, ih (fun i => γ i.succ), psi_h]
    by_cases h0 : γ 0 = 0
    · have e1 : (∀ i, γ i = 0) ↔ ∀ i : Fin r, γ i.succ = 0 := by
        constructor
        · intro h i; exact h _
        · intro h i; refine Fin.cases h0 (fun i => h i) i
      have e2 : (∃ j, γ = Pi.single j k) ↔ ∃ j : Fin r, (fun i => γ i.succ) = Pi.single j k := by
        constructor
        · rintro ⟨j, hj⟩
          refine Fin.cases (fun hj => ?_) (fun j hj => ⟨j, ?_⟩) j hj
          · have := congrFun hj 0; simp at this; omega
          · funext i; rw [hj]; simp [Pi.single_apply, Fin.succ_inj]
        · rintro ⟨j, hj⟩
          refine ⟨j.succ, ?_⟩
          funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [h0, Pi.single_apply, (Fin.succ_ne_zero j).symm]
          · have := congrFun hj i; simp only at this; rw [this]; simp [Pi.single_apply, Fin.succ_inj]
      simp only [h0, if_true, one_mul, e1, e2]
    · by_cases hk' : γ 0 = k
      · have e1 : ¬ ∀ i, γ i = 0 := fun h => h0 (h 0)
        have e2 : (∃ j, γ = Pi.single j k) ↔ ∀ i : Fin r, γ i.succ = 0 := by
          constructor
          · rintro ⟨j, hj⟩ i
            have hj0 : j = 0 := by
              by_contra hne
              have := congrFun hj 0
              rw [Pi.single_apply, if_neg (Ne.symm hne)] at this
              exact h0 this
            subst hj0
            rw [hj]; simp [Pi.single_apply, Fin.succ_ne_zero]
          · intro h
            refine ⟨0, ?_⟩
            funext i
            refine Fin.cases ?_ (fun i => ?_) i
            · simp [hk']
            · simp [h i, Pi.single_apply, Fin.succ_ne_zero]
        rw [if_neg h0, if_pos hk', if_neg e1]
        by_cases hall : ∀ i : Fin r, γ i.succ = 0
        · rw [if_pos hall, if_pos (e2.mpr hall)]; simp
        · rw [if_neg hall, if_neg (fun h => hall (e2.mp h))]
          split_ifs <;> simp [DualNumber.eps_mul_eps]
      · have e1 : ¬ ∀ i, γ i = 0 := fun h => h0 (h 0)
        have e2 : ¬ ∃ j, γ = Pi.single j k := by
          rintro ⟨j, hj⟩
          have := congrFun hj 0
          rw [Pi.single_apply] at this
          split_ifs at this <;> omega
        rw [if_neg h0, if_neg hk', if_neg e1, if_neg e2, zero_mul]

theorem snd_psi_word {r : ℕ} (k : ℕ) (hk : 0 < k) (γ : Fin r → ℕ) :
    (psi k (EKMixedPairing.word γ (fun _ => false))).snd =
      if (∃ j, γ = Pi.single j k) then 1 else 0 := by
  rw [EKCenterPower.psi_word, psi_prod k hk]
  by_cases h1 : ∀ i, γ i = 0
  · have : ¬ ∃ j, γ = Pi.single j k := by
      rintro ⟨j, hj⟩
      have := congrFun hj j
      rw [h1 j, Pi.single_eq_same] at this
      omega
    rw [if_pos h1, if_neg this]; rfl
  · rw [if_neg h1]
    split_ifs <;> rfl

theorem single_inj {r k : ℕ} (hk : 0 < k) {i j : Fin r}
    (h : (Pi.single i k : Fin r → ℕ) = Pi.single j k) : i = j := by
  by_contra hne
  have := congrFun h i
  rw [Pi.single_eq_same, Pi.single_apply, if_neg hne] at this
  omega

theorem split_sum_single {r : ℕ} (β : Fin r → ℕ) (k : ℕ) (j : Fin r) (G : (Fin r → ℕ) → ℤ) :
    ∑ u : Splits β, (if upper u = Pi.single j k then G (lower u) else 0) =
      if k ≤ β j then G (Function.update β j (β j - k)) else 0 := by
  classical
  by_cases hkj : k ≤ β j
  · rw [if_pos hkj]
    have hle : ∀ i, (Pi.single j k : Fin r → ℕ) i < β i + 1 := by
      intro i
      rw [Pi.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
    let u0 : Splits β := fun i => ⟨(Pi.single j k : Fin r → ℕ) i, hle i⟩
    have hu0 : upper u0 = Pi.single j k := rfl
    rw [Fintype.sum_eq_single u0]
    · rw [if_pos hu0]
      congr 1
      funext i
      simp only [lower, u0, Function.update_apply, Pi.single_apply]
      split_ifs with h
      · subst h; rfl
      · simp
    · intro u hu
      rw [if_neg]
      intro h
      apply hu
      funext i
      apply Fin.ext
      exact congrFun h i
  · rw [if_neg hkj]
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg]
    intro h
    have h1 := congrFun h j
    have h2 := (u j).isLt
    simp only [upper, Pi.single_eq_same] at h1
    omega

/-- Left multiplication by `p_{2a}` against an `h`-word: `(p_{2a} Y, h_β) =
Σ_{j : 2a ≤ β_j} (Y, h_{β - 2a e_j})`. -/
theorem pairing_p_mul (a : ℕ) (ha : 0 < a) (Y : Q) {r : ℕ} (β : Fin r → ℕ) :
    quotientPairing (p (2 * a) * Y) (hw β) =
      ∑ j, if 2 * a ≤ β j then quotientPairing Y (hw (Function.update β j (β j - 2 * a))) else 0 := by
  classical
  obtain ⟨P, hP⟩ := pi_surjective (p (2 * a))
  obtain ⟨Y', rfl⟩ := pi_surjective Y
  have hk : 0 < 2 * a := by omega
  rw [← hP, ← map_mul, hw, quotientPairing_pi, EKCenterPowerControls.pairing_mul_word]
  simp only [pairing_lift hP, phi_pi (2 * a) hk (even_two_mul a), snd_psi_word _ hk, hw,
    quotientPairing_pi]
  have step : ∀ u : Splits β, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
      ((if ∃ j, upper u = Pi.single j (2 * a) then 1 else 0) *
        pairing Y' (EKMixedPairing.word (lower u) fun _ => false)) =
      ∑ j, (if upper u = Pi.single j (2 * a) then
        pairing Y' (EKMixedPairing.word (lower u) fun _ => false) else 0) := by
    intro u
    by_cases hex : ∃ j, upper u = Pi.single j (2 * a)
    · obtain ⟨j0, hj0⟩ := hex
      rw [if_pos ⟨j0, hj0⟩, Finset.sum_eq_single j0]
      · rw [if_pos hj0, one_mul]
        have he : Even (crossCols (upper u) (lower u)) := by
          apply EKCenterPower.crossCols_even_left
          intro i
          rw [hj0, Pi.single_apply]
          split_ifs
          · exact even_two_mul a
          · exact Even.zero
        rw [he.neg_one_pow, one_mul]
      · intro j _ hj
        rw [if_neg]
        intro h
        exact hj (single_inj hk (h.symm.trans hj0))
      · simp
    · rw [if_neg hex, zero_mul, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hex ⟨j, h⟩)]
  rw [Finset.sum_congr rfl (fun u _ => step u), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact split_sum_single β (2 * a) j (fun v => pairing Y' (EKMixedPairing.word v fun _ => false))

/-! ## Products of the `p_{2a}` against `h`-words -/

/-- `p_{2L} = p_{2L₁} ⋯ p_{2L_r}`. -/
def pL (L : List ℕ) : Q := (L.map (fun a => p (2 * a))).prod

/-- `N(L, β) = (p_{2L}, h_β)`. -/
def pairN (L : List ℕ) {r : ℕ} (β : Fin r → ℕ) : ℤ := quotientPairing (pL L) (hw β)

theorem pairN_nil {r : ℕ} (β : Fin r → ℕ) : pairN [] β = if ∑ j, β j = 0 then 1 else 0 := by
  rw [pairN, pL, List.map_nil, List.prod_nil, hw, ← map_one pi, quotientPairing_pi,
    ← EKMixedPairing.gen_zero false, EKMixedPairing.pairing_gen_word]
  by_cases h : ∑ j, β j = 0
  · rw [if_pos h.symm, if_pos h]
    apply Finset.prod_eq_one
    intro j _
    simp [EKMixedPairing.cell]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem pairN_cons (a : ℕ) (ha : 0 < a) (L : List ℕ) {r : ℕ} (β : Fin r → ℕ) :
    pairN (a :: L) β =
      ∑ j, if 2 * a ≤ β j then pairN L (Function.update β j (β j - 2 * a)) else 0 := by
  rw [pairN, pL, List.map_cons, List.prod_cons, pairing_p_mul a ha]
  rfl

theorem pairN_nonneg (L : List ℕ) (hL : ∀ a ∈ L, 0 < a) {r : ℕ} (β : Fin r → ℕ) :
    0 ≤ pairN L β := by
  induction L generalizing β with
  | nil => rw [pairN_nil]; split_ifs <;> norm_num
  | cons a L ih =>
    rw [pairN_cons a (hL a (by simp))]
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact ih (fun b hb => hL b (by simp [hb])) _
    · exact le_refl 0

/-- The multiset of nonzero entries of a tuple. -/
def nz {r : ℕ} (β : Fin r → ℕ) : Multiset ℕ :=
  (Finset.univ.filter (fun j => β j ≠ 0)).val.map β

theorem nz_update_zero {r : ℕ} (β : Fin r → ℕ) (j : Fin r) (hj : β j ≠ 0) :
    nz β = β j ::ₘ nz (Function.update β j 0) := by
  classical
  have hs : Finset.univ.filter (fun i => β i ≠ 0) =
      insert j (Finset.univ.filter (fun i => Function.update β j 0 i ≠ 0)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Function.update_apply]
    by_cases h : i = j
    · subst h; simp [hj]
    · simp [h]
  have hnot : j ∉ Finset.univ.filter (fun i => Function.update β j 0 i ≠ 0) := by simp
  rw [nz, nz, hs, Finset.insert_val_of_not_mem hnot, Multiset.map_cons]
  congr 1
  apply Multiset.map_congr rfl
  intro i hi
  have : i ≠ j := by
    intro h; subst h; simp at hi
  rw [Function.update_of_ne this]

theorem card_nz_update {r : ℕ} (β : Fin r → ℕ) (j : Fin r) (x : ℕ) (hj : β j ≠ 0) (hx : x ≠ 0) :
    Multiset.card (nz (Function.update β j x)) = Multiset.card (nz β) := by
  classical
  simp only [nz, Multiset.card_map, Finset.card_val]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
  by_cases h : i = j
  · subst h; simp [hj, hx]
  · simp [h]

theorem nz_zero {r : ℕ} (β : Fin r → ℕ) (h : ∀ j, β j = 0) : nz β = 0 := by
  simp [nz, h]

/-- Support of `N(L, β)`: at most `ℓ(L)` nonzero parts, and exactly the parts `2L` when there
are `ℓ(L)` of them. -/
theorem pairN_support (L : List ℕ) (hL : ∀ a ∈ L, 0 < a) {r : ℕ} (β : Fin r → ℕ)
    (hN : pairN L β ≠ 0) :
    Multiset.card (nz β) ≤ L.length ∧
      (Multiset.card (nz β) = L.length → nz β = ((L.map (2 * ·) : List ℕ) : Multiset ℕ)) := by
  induction L generalizing β with
  | nil =>
    rw [pairN_nil] at hN
    have h0 : ∑ j, β j = 0 := by by_contra h; rw [if_neg h] at hN; exact hN rfl
    have hall : ∀ j, β j = 0 := fun j => (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ j)
    rw [nz_zero β hall]
    simp
  | cons a L ih =>
    have ha : 0 < a := hL a (by simp)
    have hL' : ∀ b ∈ L, 0 < b := fun b hb => hL b (by simp [hb])
    rw [pairN_cons a ha] at hN
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hN
    have hle : 2 * a ≤ β j := by by_contra h; rw [if_neg h] at hj; exact hj rfl
    rw [if_pos hle] at hj
    obtain ⟨ih1, ih2⟩ := ih hL' _ hj
    have hbj : β j ≠ 0 := by omega
    by_cases hz : β j - 2 * a = 0
    · have hβj : β j = 2 * a := by omega
      rw [hz] at ih1 ih2
      rw [nz_update_zero β j hbj, Multiset.card_cons, hβj]
      refine ⟨by simp; omega, fun hc => ?_⟩
      rw [ih2 (by simp at hc; omega)]
      simp
    · have hc := card_nz_update β j (β j - 2 * a) hbj hz
      rw [hc] at ih1
      refine ⟨by simp; omega, fun he => ?_⟩
      simp at he
      omega

/-- The test tuple `2L`. -/
def twoVec (L : List ℕ) : Fin L.length → ℕ := fun i => 2 * L.get i

theorem nz_twoVec (L : List ℕ) (hL : ∀ a ∈ L, 0 < a) :
    nz (twoVec L) = ((L.map (2 * ·) : List ℕ) : Multiset ℕ) := by
  have hf : Finset.univ.filter (fun j => twoVec L j ≠ 0) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, twoVec]
    have := hL (L.get j) (List.get_mem L j)
    omega
  rw [nz, hf, Fin.univ_val_map]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp [twoVec]

theorem hw_cons_zero {r : ℕ} (γ : Fin r → ℕ) : hw (Fin.cons 0 γ : Fin (r + 1) → ℕ) = hw γ := by
  simp only [hw, EKMixedPairing.word_succ, Fin.cons_zero, EKMixedPairing.gen_zero, one_mul,
    Fin.cons_succ]

theorem pairN_diag_pos (L : List ℕ) (hL : ∀ a ∈ L, 0 < a) : 0 < pairN L (twoVec L) := by
  induction L with
  | nil => rw [pairN_nil]; simp
  | cons a L ih =>
    have ha : 0 < a := hL a (by simp)
    have hL' : ∀ b ∈ L, 0 < b := fun b hb => hL b (by simp [hb])
    rw [pairN_cons a ha]
    have hterm : ∀ j ∈ Finset.univ, 0 ≤ (if 2 * a ≤ twoVec (a :: L) j then
        pairN L (Function.update (twoVec (a :: L)) j (twoVec (a :: L) j - 2 * a)) else 0) := by
      intro j _
      split_ifs
      · exact pairN_nonneg L hL' _
      · exact le_refl 0
    let z0 : Fin (a :: L).length := ⟨0, by simp⟩
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm (Finset.mem_univ z0))
    have h0 : twoVec (a :: L) z0 = 2 * a := rfl
    rw [if_pos (le_of_eq h0.symm)]
    have hv : Function.update (twoVec (a :: L)) z0 (twoVec (a :: L) z0 - 2 * a) =
        (Fin.cons 0 (twoVec L) : Fin (L.length + 1) → ℕ) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · show Function.update (twoVec (a :: L)) z0 (twoVec (a :: L) z0 - 2 * a) z0 = 0
        rw [Function.update_self, h0, Nat.sub_self]
      · have hne : (Fin.succ i : Fin (a :: L).length) ≠ z0 := by
          intro h; have := congrArg Fin.val h; simp [z0] at this
        rw [Function.update_of_ne hne]
        simp [twoVec]
    rw [hv, pairN, hw_cons_zero]
    exact ih hL'

/-! ## Linear independence of the monomials `p_{2λ}` -/

/-- `p_{2λ} = p_{2λ₁} ⋯ p_{2λ_r}` for a partition `λ`. -/
def pP (μ : YoungDiagram) : Q := pL μ.rowLens

theorem rowLens_eq_of_map_two {μ ν : YoungDiagram}
    (h : ((μ.rowLens.map (2 * ·) : List ℕ) : Multiset ℕ) = ((ν.rowLens.map (2 * ·) : List ℕ) : Multiset ℕ)) :
    μ = ν := by
  rw [← Multiset.map_coe, ← Multiset.map_coe] at h
  have h' := Multiset.map_injective (f := (2 * ·)) (fun a b hab => by simpa using hab) h
  have hp : μ.rowLens.Perm ν.rowLens := Multiset.coe_eq_coe.mp h'
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext (List.eq_of_perm_of_sorted hp μ.rowLens_sorted ν.rowLens_sorted)

/-- **Linear independence of the `p_{2λ}`**, `λ` over all partitions (all degrees). -/
theorem pP_linearIndependent : LinearIndependent ℤ pP := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let s' := s.filter (fun j => g j ≠ 0)
  have hs' : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨l0, hl0, hmax⟩ := Finset.exists_max_image s' (fun j => j.rowLens.length) hs'
  have hl0' := Finset.mem_filter.mp hl0
  have hpos0 : ∀ a ∈ l0.rowLens, 0 < a := l0.pos_of_mem_rowLens
  have hp := congrArg (fun x => quotientPairing x (hw (twoVec l0.rowLens))) hsum
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, map_zero, LinearMap.zero_apply] at hp
  rw [Finset.sum_eq_single l0] at hp
  · have := pairN_diag_pos l0.rowLens hpos0
    rw [pairN] at this
    have hz := mul_eq_zero.mp hp
    rcases hz with hz | hz
    · exact hl0'.2 hz
    · rw [pP] at hz; omega
  · intro j hj hne
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hN : pairN j.rowLens (twoVec l0.rowLens) = 0 := by
        by_contra hN
        obtain ⟨h1, h2⟩ := pairN_support j.rowLens j.pos_of_mem_rowLens _ hN
        rw [nz_twoVec _ hpos0] at h1 h2
        simp only [Multiset.coe_card, List.length_map] at h1 h2
        have h3 := hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
        exact hne (rowLens_eq_of_map_two (h2 (by omega))).symm
      rw [pP]
      rw [pairN] at hN
      rw [hN, mul_zero]
  · intro h; exact absurd hl0'.1 h

/-! ## Algebraic independence in the centre -/

theorem p_even_central (k : ℕ) : p (2 * (k + 1)) ∈ Subring.center Q := by
  rw [Subring.mem_center_iff]
  intro y
  exact ((EKCenterPower.center_iff (2 * (k + 1)) (by omega)).mpr (even_two_mul _) y).symm

/-- `p_{2(k+1)}` as an element of the (commutative) centre of `Q`. -/
def pc (k : ℕ) : Subring.center Q := ⟨p (2 * (k + 1)), p_even_central k⟩

theorem finsupp_prod_eq (s : ℕ →₀ ℕ) :
    (s.prod fun k n => pc k ^ n) = (s.toMultiset.map pc).prod := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a n f ha hn ih =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun k n => pc k ^ n) (pow_zero _), ih, Finsupp.toMultiset_add, Multiset.map_add,
      Multiset.prod_add, Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.map_singleton,
      Multiset.prod_nsmul, Multiset.prod_singleton]

/-- The partition with `s k` parts equal to `k + 1`. -/
def sortL (s : ℕ →₀ ℕ) : List ℕ := Multiset.sort (· ≥ ·) (s.toMultiset.map (· + 1))

theorem sortL_sorted (s : ℕ →₀ ℕ) : (sortL s).Sorted (· ≥ ·) := Multiset.sort_sorted _ _

theorem sortL_coe (s : ℕ →₀ ℕ) : ((sortL s : List ℕ) : Multiset ℕ) = s.toMultiset.map (· + 1) :=
  Multiset.sort_eq _ _

theorem sortL_pos (s : ℕ →₀ ℕ) : ∀ a ∈ sortL s, 0 < a := by
  intro a ha
  rw [← Multiset.mem_coe, sortL_coe, Multiset.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  omega

def shapeOf (s : ℕ →₀ ℕ) : YoungDiagram := YoungDiagram.ofRowLens (sortL s) (sortL_sorted s)

theorem shapeOf_rowLens (s : ℕ →₀ ℕ) : (shapeOf s).rowLens = sortL s :=
  YoungDiagram.rowLens_ofRowLens_eq_self (sortL_pos s)

theorem shapeOf_injective : Function.Injective shapeOf := by
  intro s t h
  have h1 := congrArg (fun μ : YoungDiagram => ((μ.rowLens : List ℕ) : Multiset ℕ)) h
  simp only [shapeOf_rowLens, sortL_coe] at h1
  have h2 := Multiset.map_injective (f := (· + 1)) (fun a b hab => by simpa using hab) h1
  classical
  rw [← Finsupp.toMultiset_toFinsupp s, ← Finsupp.toMultiset_toFinsupp t, h2]

theorem monomial_coe (s : ℕ →₀ ℕ) :
    ((s.prod fun k n => pc k ^ n : Subring.center Q) : Q) = pP (shapeOf s) := by
  rw [finsupp_prod_eq, pP, pL, shapeOf_rowLens]
  have hm : s.toMultiset.map pc = ((sortL s).map (fun a => pc (a - 1)) : List _) := by
    rw [← Multiset.map_coe, sortL_coe, Multiset.map_map]
    rfl
  rw [hm, Multiset.prod_coe, ← Subring.coe_subtype, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  have := sortL_pos s a ha
  simp only [Function.comp_apply, Subring.coe_subtype, pc]
  congr 2
  omega

/-- **Algebraic independence of the `p_{2k}`** (EK p. 26): the elements `p_2, p_4, p_6, …` of
the centre of `Q` are algebraically independent over `ℤ`. -/
theorem algebraicIndependent_p : AlgebraicIndependent ℤ pc := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  have hli : LinearIndependent ℤ (fun s : ℕ →₀ ℕ => pP (shapeOf s)) :=
    pP_linearIndependent.comp shapeOf shapeOf_injective
  have hsum : ∑ s ∈ P.support, P.coeff s • pP (shapeOf s) = 0 := by
    have h := congrArg (fun z : Subring.center Q => (z : Q)) hP
    simp only at h
    rw [P.as_sum, map_sum] at h
    simp only [MvPolynomial.aeval_monomial, Subring.coe_zero] at h
    rw [← h]
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    rw [← monomial_coe, Algebra.algebraMap_eq_smul_one]
    simp only [Subring.coe_mul, zsmul_eq_mul, Subring.coe_intCast, mul_one]
  ext s
  by_cases hs : s ∈ P.support
  · exact linearIndependent_iff'.mp hli P.support (fun s => P.coeff s) hsum s hs
  · simpa using hs

end OddMath.Frontier.EKRest

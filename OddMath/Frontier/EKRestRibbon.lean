import OddMath.Frontier.EKGeneralQ

/-! # EK (2.33): the form on the basis `h̃_α` counts permutations by descent compositions

EK arXiv:1107.5610v2, §2.4, p. 22, at arbitrary `q` in an arbitrary commutative ring `k`,
for the form (2.1) on `Λ′` (`EKGeneralQ.form`).

Compositions of `n` are encoded by their cut sets `S ⊆ {1, …, n-1}` (the partial sums
`a₁, a₁+a₂, …`); `α ≤ β`-refinement is inclusion of cut sets, and `ℓ(α) = |S(α)| + 1`.
`hS S` is `h_α` for the composition with cut set `S`, and (2.31) reads
`h̃_α = Σ_{β ≤ α} (-1)^{ℓ(α)-ℓ(β)} h_β = Σ_{T ⊆ S(α)} (-1)^{|S(α)|-|T|} h_{α(T)}` (`hT`).
For `σ ∈ S_n`, the descent composition `C(σ)` has cut set `Des σ = {k : σ(k) < σ(k-1)}`
(0-indexed positions).

* `form_hS`: `(h_β, h_α) = Σ_{σ : Des σ ⊆ S(α), Des σ⁻¹ ⊆ S(β)} q^{ℓ(σ)}` (minimal double-coset
  representatives, `EKPlatformBijection.minimalPermEquiv`);
* `eq_2_33`: `(h̃_β, h̃_α) = Σ_{σ : C(σ) = α, C(σ⁻¹) = β} q^{ℓ(σ)}` (inclusion–exclusion).

Here `ℓ(σ)` is the inversion number `EKPlatformBijection.inversions`, and `σ` maps bottom
endpoints to top endpoints (the convention of `EKPlatformBijection`).
-/

noncomputable section
open scoped BigOperators

namespace OddMath.Frontier.EKRest
open EKPairingMatrices EKPlatformBijection EKGeneralQ

variable {k : Type*} [CommRing k] (q : k)

open Classical in
/-- The margin-matrix form as a sum over permutations with no crossing inside a platform. -/
theorem matForm_perm {n r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) (h1 : (∑ i, β i) = n)
    (h2 : (∑ j, α j) = n) :
    matForm q β α = ∑ σ ∈ Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => NoWithin (endpoint β h1) (endpoint α h2) σ),
        q ^ inversions σ := by
  subst h1
  rw [matForm, Finset.sum_subtype (Finset.univ.filter _)
    (p := fun σ => NoWithin (endpoint β rfl) (endpoint α h2) σ) (fun σ => by simp)]
  symm
  apply Fintype.sum_equiv (minimalPermEquiv β α h2.symm)
  intro σ
  congr 1
  show inversions σ.val = crossing (diagramMatrix (permDiagram β α h2.symm σ)).val
  exact ((permDiagram β α h2.symm σ).val.crossing_eq_length).symm

/-! ## Compositions as cut sets -/

/-- The predecessor position `k - 1`. -/
def pred' {n : ℕ} (k : Fin n) : Fin n := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- Number of (positive) cuts `≤ a`: the block containing position `a`. -/
def blk {n : ℕ} (S : Finset (Fin n)) (a : Fin n) : ℕ :=
  (S.filter (fun s => 0 < s.val ∧ s ≤ a)).card

/-- Number of positive cuts; the composition has `ncut S + 1` parts. -/
def ncut {n : ℕ} (S : Finset (Fin n)) : ℕ := (S.filter (fun s => 0 < s.val)).card

theorem blk_le {n : ℕ} (S : Finset (Fin n)) (a : Fin n) : blk S a ≤ ncut S :=
  Finset.card_le_card (fun s hs => by simp only [Finset.mem_filter] at hs ⊢; exact ⟨hs.1, hs.2.1⟩)

/-- The block map of the composition with cut set `S`. -/
def blockMap {n : ℕ} (S : Finset (Fin n)) (a : Fin n) : Fin (ncut S + 1) :=
  ⟨blk S a, Nat.lt_succ_of_le (blk_le S a)⟩

theorem blockMap_monotone {n : ℕ} (S : Finset (Fin n)) : Monotone (blockMap S) := by
  intro a b hab
  show blk S a ≤ blk S b
  exact Finset.card_le_card (fun s hs => by
    simp only [Finset.mem_filter] at hs ⊢; exact ⟨hs.1, hs.2.1, le_trans hs.2.2 hab⟩)

/-- The parts of the composition with cut set `S`. -/
def parts {n : ℕ} (S : Finset (Fin n)) (i : Fin (ncut S + 1)) : ℕ :=
  ∑ a, if blockMap S a = i then 1 else 0

theorem parts_sum {n : ℕ} (S : Finset (Fin n)) : (∑ i, parts S i) = n := by
  unfold parts
  rw [Finset.sum_comm]
  simp

theorem endpoint_parts {n : ℕ} (S : Finset (Fin n)) :
    endpoint (parts S) (parts_sum S) = blockMap S :=
  (endpoint_unique (parts S) (parts_sum S) (blockMap_monotone S) (fun _ => rfl)).symm

/-- Two positions `a ≤ b` lie in the same block iff no cut lies in `(a, b]`. -/
theorem blockMap_eq_iff {n : ℕ} (S : Finset (Fin n)) {a b : Fin n} (hab : a ≤ b) :
    blockMap S a = blockMap S b ↔ ∀ s ∈ S, 0 < s.val → ¬ (a < s ∧ s ≤ b) := by
  constructor
  · intro h s hs hs0 ⟨h1, h2⟩
    have hsub : S.filter (fun t => 0 < t.val ∧ t ≤ a) ⊂ S.filter (fun t => 0 < t.val ∧ t ≤ b) := by
      refine ⟨fun t ht => ?_, fun hsup => ?_⟩
      · simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1, le_trans ht.2.2 hab⟩
      · have := hsup (Finset.mem_filter.mpr ⟨hs, hs0, h2⟩)
        simp only [Finset.mem_filter] at this
        exact absurd this.2.2 (not_le.mpr h1)
    have := Finset.card_lt_card hsub
    have h' := congrArg Fin.val h
    simp only [blockMap, blk] at h'
    omega
  · intro h
    apply Fin.ext
    show blk S a = blk S b
    unfold blk
    congr 1
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, ht0, hta⟩; exact ⟨ht, ht0, le_trans hta hab⟩
    · rintro ⟨ht, ht0, htb⟩
      refine ⟨ht, ht0, ?_⟩
      by_contra hc
      exact h t ht ht0 ⟨lt_of_not_le hc, htb⟩

/-- The descent set `{k : σ(k) < σ(k-1)}` (cut set of the descent composition `C(σ)`). -/
def Des {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun k => 0 < k.val ∧ σ k < σ (pred' k))

theorem pred'_lt {n : ℕ} {k : Fin n} (hk : 0 < k.val) : pred' k < k := by
  rw [Fin.lt_def]; simp [pred']; omega

theorem chain {n : ℕ} (f : Fin n → Fin n) (a : Fin n) :
    ∀ b : Fin n, a < b → (∀ k : Fin n, a < k → k ≤ b → f (pred' k) < f k) → f a < f b := by
  intro b
  induction' hb : b.val with m ih generalizing b
  · intro h; exact absurd h (by rw [Fin.lt_def]; omega)
  · intro hab h
    have hb0 : 0 < b.val := by omega
    by_cases hpa : pred' b = a
    · have := h b hab le_rfl; rwa [hpa] at this
    · have hapb : a < pred' b := by
        rw [Fin.lt_def] at hab ⊢
        have : (pred' b).val ≠ a.val := fun e => hpa (Fin.ext e)
        simp [pred'] at this ⊢; omega
      have h1 := ih (pred' b) (by simp [pred']; omega) hapb (fun k hk1 hk2 =>
        h k hk1 (le_trans hk2 (le_of_lt (pred'_lt hb0))))
      exact lt_trans h1 (h b hab le_rfl)

/-- Consecutive positions `k - 1, k` share a block iff `k` is not a cut. -/
theorem blockMap_pred {n : ℕ} (S : Finset (Fin n)) {k : Fin n} (hk : 0 < k.val) :
    blockMap S (pred' k) = blockMap S k ↔ k ∉ S := by
  rw [blockMap_eq_iff S (le_of_lt (pred'_lt hk))]
  constructor
  · intro h hkS; exact h k hkS hk ⟨pred'_lt hk, le_rfl⟩
  · intro h s hs _ ⟨h1, h2⟩
    have : s = k := by
      apply Fin.ext
      rw [Fin.lt_def] at h1; rw [Fin.le_def] at h2
      simp [pred'] at h1; omega
    exact h (this ▸ hs)

theorem not_mem_of_same {n : ℕ} (S : Finset (Fin n)) {a b : Fin n} (hab : a < b)
    (h : blockMap S a = blockMap S b) {k : Fin n} (hk1 : a < k) (hk2 : k ≤ b) : k ∉ S := by
  intro hkS
  have hk0 : 0 < k.val := by rw [Fin.lt_def] at hk1; omega
  exact (blockMap_eq_iff S (le_of_lt hab)).mp h k hkS hk0 ⟨hk1, hk2⟩

theorem incr_of_not_des {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : Fin n} (hk : 0 < k.val)
    (hd : k ∉ Des σ) : σ (pred' k) < σ k := by
  simp only [Des, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hd
  have hne : σ (pred' k) ≠ σ k := fun h => (ne_of_lt (pred'_lt hk)) (σ.injective h)
  exact lt_of_le_of_ne (hd hk) hne

/-- The no-crossing-within-a-platform condition is `Des σ ⊆ S(α)`, `Des σ⁻¹ ⊆ S(β)`. -/
theorem noWithin_iff {n : ℕ} (S R : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    NoWithin (blockMap S) (blockMap R) σ ↔ Des σ ⊆ R ∧ Des σ⁻¹ ⊆ S := by
  constructor
  · intro h
    constructor
    · intro k hk
      by_contra hkR
      simp only [Des, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have := h (pred' k) k (pred'_lt hk.1) (Or.inl ((blockMap_pred R hk.1).mpr hkR))
      exact absurd hk.2 (not_lt.mpr (le_of_lt this))
    · intro k hk
      by_contra hkS
      simp only [Des, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have := h (σ⁻¹ k) (σ⁻¹ (pred' k)) hk.2 (Or.inr (by
        simp only [Equiv.Perm.apply_inv_self]; exact ((blockMap_pred S hk.1).mpr hkS).symm))
      simp only [Equiv.Perm.apply_inv_self] at this
      exact absurd this (not_lt.mpr (le_of_lt (pred'_lt hk.1)))
  · rintro ⟨hR, hS⟩ a b hab hw
    rcases hw with hw | hw
    · apply chain σ a b hab
      intro k hk1 hk2
      have hk0 : 0 < k.val := by rw [Fin.lt_def] at hk1; omega
      exact incr_of_not_des σ hk0 (fun hd => not_mem_of_same R hab hw hk1 hk2 (hR hd))
    · by_contra hc
      have hlt : σ b < σ a := lt_of_le_of_ne (not_lt.mp hc)
        (fun e => (ne_of_lt hab) (σ.injective e).symm)
      have := chain (⇑(σ⁻¹)) (σ b) (σ a) hlt (fun k hk1 hk2 => by
        have hk0 : 0 < k.val := by rw [Fin.lt_def] at hk1; omega
        exact incr_of_not_des σ⁻¹ hk0 (fun hd => not_mem_of_same S hlt hw.symm hk1 hk2 (hS hd)))
      simp only [Equiv.Perm.inv_apply_self] at this
      exact absurd hab (not_lt.mpr (le_of_lt this))

/-! ## The form on `h_α` and on `h̃_α` -/

/-- `h_α` for the composition with cut set `S`. -/
def hS {n : ℕ} (S : Finset (Fin n)) : L k := vWord k (parts S)

open Classical in
/-- `(h_β, h_α) = Σ_{σ : Des σ ⊆ S(α), Des σ⁻¹ ⊆ S(β)} q^{ℓ(σ)}`. -/
theorem form_hS {n : ℕ} (S R : Finset (Fin n)) :
    form q (hS (k := k) S) (hS R) =
      ∑ σ : Equiv.Perm (Fin n), if Des σ ⊆ R ∧ Des σ⁻¹ ⊆ S then q ^ inversions σ else 0 := by
  rw [hS, hS, form_vWord, matForm_perm q _ _ (parts_sum S) (parts_sum R), endpoint_parts,
    endpoint_parts, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [noWithin_iff]

/-- Inclusion–exclusion on cut sets: `Σ_{T ⊆ S} (-1)^{|S|-|T|} [D ⊆ T] = [D = S]`. -/
theorem incl_excl {α : Type*} [DecidableEq α] (S D : Finset α) :
    ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S.card - T.card) * (if D ⊆ T then 1 else 0) =
      if D = S then 1 else 0 := by
  induction S using Finset.induction_on generalizing D with
  | empty =>
    rw [Finset.powerset_empty, Finset.sum_singleton]
    simp [Finset.subset_empty]
  | insert a S ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h1 : ∀ T ∈ S.powerset, (-1 : ℤ) ^ ((insert a S).card - T.card) *
        (if D ⊆ T then 1 else 0) = -((-1 : ℤ) ^ (S.card - T.card) * (if D ⊆ T then 1 else 0)) := by
      intro T hT
      have hTS := Finset.card_le_card (Finset.mem_powerset.mp hT)
      rw [Finset.card_insert_of_not_mem ha, show S.card + 1 - T.card = (S.card - T.card) + 1 by omega,
        pow_succ]
      ring
    have h2 : ∀ T ∈ S.powerset, (-1 : ℤ) ^ ((insert a S).card - (insert a T).card) *
        (if D ⊆ insert a T then 1 else 0) =
          (-1 : ℤ) ^ (S.card - T.card) * (if D.erase a ⊆ T then 1 else 0) := by
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      rw [Finset.card_insert_of_not_mem ha, Finset.card_insert_of_not_mem haT,
        Nat.add_sub_add_right]
      simp only [Finset.subset_insert_iff]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib, ih, ih]
    by_cases haD : a ∈ D
    · have e1 : D ≠ S := fun h => ha (h ▸ haD)
      have e2 : D.erase a = S ↔ D = insert a S := by
        constructor
        · intro h; rw [← h, Finset.insert_erase haD]
        · intro h; rw [h, Finset.erase_insert ha]
      rw [if_neg e1]
      by_cases h3 : D = insert a S
      · rw [if_pos (e2.mpr h3), if_pos h3]; ring
      · rw [if_neg (fun h => h3 (e2.mp h)), if_neg h3]; ring
    · rw [Finset.erase_eq_of_not_mem haD]
      have : D ≠ insert a S := fun h => haD (h ▸ Finset.mem_insert_self a S)
      rw [if_neg this]
      split_ifs <;> ring

/-- (2.31): `h̃_α = Σ_{β ≤ α} (-1)^{ℓ(α)-ℓ(β)} h_β`, `S = S(α)`. -/
def hT {n : ℕ} (S : Finset (Fin n)) : L k :=
  ∑ T ∈ S.powerset, ((-1 : ℤ) ^ (S.card - T.card)) • hS (k := k) T

open Classical in
/-- **EK (2.33), p. 22:** `(h̃_β, h̃_α) = Σ_{σ ∈ S_n, C(σ) = α, C(σ⁻¹) = β} q^{ℓ(σ)}`,
with `S = S(β)`, `R = S(α)`. -/
theorem eq_2_33 {n : ℕ} (S R : Finset (Fin n)) :
    form q (hT (k := k) S) (hT R) =
      ∑ σ : Equiv.Perm (Fin n), if Des σ = R ∧ Des σ⁻¹ = S then q ^ inversions σ else 0 := by
  have step : ∀ (T R' : Finset (Fin n)) (σ : Equiv.Perm (Fin n)),
      ((-1 : ℤ) ^ (R.card - R'.card)) • (((-1 : ℤ) ^ (S.card - T.card)) •
        (if Des σ ⊆ R' ∧ Des σ⁻¹ ⊆ T then q ^ inversions σ else 0)) =
      (((-1 : ℤ) ^ (S.card - T.card) * (if Des σ⁻¹ ⊆ T then 1 else 0)) *
        ((-1 : ℤ) ^ (R.card - R'.card) * (if Des σ ⊆ R' then 1 else 0))) • q ^ inversions σ := by
    intro T R' σ
    by_cases h1 : Des σ ⊆ R' <;> by_cases h2 : Des σ⁻¹ ⊆ T <;>
      simp [h1, h2, smul_smul, zsmul_eq_mul]
    ring
  simp only [hT, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, form_hS,
    Finset.smul_sum, step]
  rw [Finset.sum_congr rfl (fun T _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [← Finset.sum_smul]
  rw [Finset.sum_comm, ← Finset.sum_mul_sum, incl_excl, incl_excl]
  by_cases h1 : Des σ = R <;> by_cases h2 : Des σ⁻¹ = S <;> simp [h1, h2]

end OddMath.Frontier.EKRest

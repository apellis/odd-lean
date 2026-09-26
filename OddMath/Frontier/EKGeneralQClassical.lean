import OddMath.Frontier.EKGeneralQCommutative
import OddMath.Frontier.EKLemma311Cond

/-!
# EK §2.1 at q = 1: unitriangularity against `e_{λᵀ}`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, pp.8–9: "Nondegeneracy of the form on the
maximal commutative quotient follows from the result that the elements `h_λ` are linearly
independent over all partitions `λ` of `n`.  This is proved by introducing elementary symmetric
functions `eₙ` via the inductive relation `Σ_{k=0}^n (-1)^k h_k e_{n-k} = 0`, defining
`e_λ = e_{λ₁} ⋯ e_{λ_r}`, and then checking that the matrix of the bilinear form is
upper-triangular with ones on the diagonal with respect to the bases `{h_λ}` and `{e_{λᵀ}}` for
any total order on partitions refining the dominance order."

Over an arbitrary commutative ring `k`, at `q = 1`, in `Λ'`:

* `eOne n`: `e₀ = 1`, `e_{n+1} = Σ_{i=0}^{n} (-1)^i h_{i+1} e_{n-i}`, i.e. the printed relation
  (`eOne_relation`);
* `form_eOne_vWord`: `(e_m, h_v) = 1` if every part of `v` is at most `1` and `|v| = m`, else `0`;
* `form_eWord_hWord`: `(e_ρ, h_β)` is the number of `0/1` matrices with row sums `ρ` and column
  sums `β`;
* `ek_q1_unitriangular`: for every linear order on partitions of `n` refining dominance, the
  matrix `A_{λμ} = (h_λ, e_{μᵀ})` is upper triangular with ones on the diagonal (vanishing by
  Gale–Ryser necessity, `EKLemma311Cond.gale_ryser`; diagonal by uniqueness of the Ferrers
  matrix, `EKSemiorthogonality.ferrers_unique`); hence `det A = 1` (`ek_q1_det`).
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKPairingMatrices DegreeShapes
open EKFreeCoproduct (W degree partWord partWord_degree)
attribute [local instance] Classical.propDecidable degreeFintype

variable {k : Type*} [CommRing k]

/-! ## Single rows -/

theorem matForm_single_row (q : k) {c : ℕ} (a : ℕ) (w : Fin c → ℕ) :
    matForm q (fun _ : Fin 1 => a) w = if (∑ j, w j) = a then 1 else 0 := by
  unfold matForm
  split_ifs with hs
  · let Z : Mat (fun _ : Fin 1 => a) w :=
      ⟨fun _ j => w j, by constructor <;> funext i <;> simp [rowSum, colSum, hs]⟩
    have hz (M : Mat (fun _ : Fin 1 => a) w) : M = Z := by
      apply Subtype.ext; funext i j
      have h := congrFun M.property.2 j
      simpa [colSum, Subsingleton.elim i 0] using h
    rw [Finset.sum_eq_single Z]
    · simp [Z, crossing]
    · intro M _ h; exact (h (hz M)).elim
    · simp
  · apply Finset.sum_eq_zero
    intro M _
    exfalso
    apply hs
    have := total_eq M
    simpa using this.symm

theorem form_h_vWord (q : k) {c : ℕ} (a : ℕ) (w : Fin c → ℕ) :
    form q (h k a) (vWord k w) = if (∑ j, w j) = a then 1 else 0 := by
  rw [← vWord_singleton, form_vWord, matForm_single_row]

/-! ## The elementary functions at q = 1 -/

variable (k) in
/-- EK p.9: `e₀ = 1` and `Σ_{i=0}^n (-1)^i hᵢ e_{n-i} = 0` for `n ≥ 1`, solved for `eₙ`. -/
def eOne : ℕ → L k
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), ((-1 : k) ^ i.val) • (h k (i.val + 1) * eOne (n - i.val))
decreasing_by all_goals omega

theorem eOne_zero : eOne k 0 = 1 := by rw [eOne]

theorem eOne_succ (n : ℕ) : eOne k (n + 1) =
    ∑ i : Fin (n + 1), ((-1 : k) ^ i.val) • (h k (i.val + 1) * eOne k (n - i.val)) := by
  rw [eOne]

/-- The printed relation `Σ_{i=0}^{n} (-1)^i hᵢ e_{n-i} = 0`, `n ≥ 1`. -/
theorem eOne_relation (n : ℕ) :
    ∑ i : Fin (n + 2), ((-1 : k) ^ i.val) • (h k i.val * eOne k (n + 1 - i.val)) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, h_zero, one_mul, Nat.sub_zero, Fin.val_succ]
  rw [eOne_succ, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have e : n + 1 - (i.val + 1) = n - i.val := by omega
  rw [e, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]

/-! ## `(e_m, h_v)` -/

theorem split_add {c : ℕ} {v : Fin c → ℕ} (u : Splits v) (j : Fin c) :
    upper u j + lower u j = v j := by
  have := (u j).isLt
  simp only [upper, lower]
  omega

theorem sum_split {c : ℕ} {v : Fin c → ℕ} (u : Splits v) :
    (∑ j, upper u j) + ∑ j, lower u j = ∑ j, v j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => split_add u j)

/-- One coordinate of the inclusion–exclusion: `Σ_{t ≤ s} (-1)^t [s - t ≤ 1] = [s = 0]`. -/
theorem alt_sum_coord (s : ℕ) :
    ∑ t : Fin (s + 1), ((-1 : k) ^ t.val * if s - t.val ≤ 1 then 1 else 0) =
      if s = 0 then 1 else 0 := by
  cases s with
  | zero => simp
  | succ s =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hz : ∀ t : Fin s, ((-1 : k) ^ (Fin.castSucc (Fin.castSucc t)).val *
        if s + 1 - (Fin.castSucc (Fin.castSucc t)).val ≤ 1 then 1 else 0) = 0 := by
      intro t
      have := t.isLt
      rw [if_neg (by simp; omega), mul_zero]
    rw [Finset.sum_eq_zero (fun t _ => hz t)]
    simp only [Fin.coe_castSucc, Fin.val_last, zero_add]
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), pow_succ]
    ring

/-- Inclusion–exclusion over splits: `Σ_u (-1)^{|u|} [v - u ≤ 1] = [v = 0]`. -/
theorem alt_sum_splits {c : ℕ} (v : Fin c → ℕ) :
    ∑ u : Splits v, ((-1 : k) ^ (∑ j, upper u j) *
      if ∀ j, lower u j ≤ 1 then 1 else 0) = if ∀ j, v j = 0 then 1 else 0 := by
  have hf : ∀ u : Splits v, ((-1 : k) ^ (∑ j, upper u j) *
      if ∀ j, lower u j ≤ 1 then 1 else 0) =
      ∏ j, ((-1 : k) ^ (u j).val * if v j - (u j).val ≤ 1 then 1 else 0) := by
    intro u
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Fintype.prod_boole]
    congr 1
    by_cases h : ∀ j, lower u j ≤ 1
    · rw [if_pos h, if_pos (show ∀ i, v i - (u i).val ≤ 1 from h)]
    · rw [if_neg h, if_neg (show ¬ ∀ i, v i - (u i).val ≤ 1 from h)]
  rw [Finset.sum_congr rfl (fun u _ => hf u)]
  rw [← Fintype.prod_sum (κ := fun j => Fin (v j + 1))
    (fun j t => ((-1 : k) ^ t.val * if v j - t.val ≤ 1 then 1 else 0))]
  simp only [alt_sum_coord]
  rw [Fintype.prod_boole]
  congr 1

theorem sum_eq_zero_iff_all {c : ℕ} (v : Fin c → ℕ) : (∑ j, v j) = 0 ↔ ∀ j, v j = 0 := by
  simp [Finset.sum_eq_zero_iff]

/-- The combinatorial identity behind `form_eOne_vWord`. -/
theorem eOne_comb (m : ℕ) {c : ℕ} (v : Fin c → ℕ) :
    ∑ i : Fin (m + 1), (-1 : k) ^ i.val * ∑ u : Splits v,
      ((if (∑ j, upper u j) = i.val + 1 then 1 else 0) *
        if (∀ j, lower u j ≤ 1) ∧ (∑ j, lower u j) = m - i.val then 1 else 0) =
      if (∀ j, v j ≤ 1) ∧ (∑ j, v j) = m + 1 then 1 else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  by_cases hS : (∑ j, v j) = m + 1
  · -- inner sum over i
    have hin : ∀ u : Splits v, (∑ i : Fin (m + 1), (-1 : k) ^ i.val *
        ((if (∑ j, upper u j) = i.val + 1 then 1 else 0) *
          if (∀ j, lower u j ≤ 1) ∧ (∑ j, lower u j) = m - i.val then 1 else 0)) =
        (if (∑ j, upper u j) = 0 then (if ∀ j, lower u j ≤ 1 then 1 else 0) else 0) -
          (-1 : k) ^ (∑ j, upper u j) * (if ∀ j, lower u j ≤ 1 then 1 else 0) := by
      intro u
      have hsp := sum_split u
      by_cases h0 : (∑ j, upper u j) = 0
      · rw [if_pos h0, h0, pow_zero, one_mul, sub_self]
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg (by omega), zero_mul, mul_zero]
      · rw [if_neg h0, zero_sub]
        obtain ⟨s, hs⟩ : ∃ s, (∑ j, upper u j) = s + 1 :=
          ⟨(∑ j, upper u j) - 1, by omega⟩
        have hsm : s < m + 1 := by omega
        rw [Finset.sum_eq_single ⟨s, hsm⟩]
        · rw [if_pos hs, one_mul, hs]
          have ht : (∑ j, lower u j) = m - s := by omega
          by_cases hL : ∀ j, lower u j ≤ 1
          · rw [if_pos ⟨hL, ht⟩, if_pos hL, pow_succ]; ring
          · rw [if_neg (fun h => hL h.1), if_neg hL]; ring
        · intro i _ hi
          rw [if_neg, zero_mul, mul_zero]
          intro h; apply hi; apply Fin.ext; simp only; omega
        · simp
    rw [Finset.sum_congr rfl (fun u _ => hin u), Finset.sum_sub_distrib, alt_sum_splits]
    rw [Finset.sum_eq_single (fun j => (0 : Fin (v j + 1)))]
    · have hv : ¬ ∀ j, v j = 0 := by
        intro h; rw [(sum_eq_zero_iff_all v).mpr h] at hS; omega
      rw [if_neg hv, sub_zero, if_pos (by simp [upper])]
      simp only [lower, Fin.val_zero, Nat.sub_zero]
      by_cases h1 : ∀ j, v j ≤ 1
      · rw [if_pos h1, if_pos ⟨h1, hS⟩]
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    · intro u _ hu
      rw [if_neg]
      intro h0
      apply hu
      funext j
      apply Fin.ext
      have := (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ j)
      simpa [upper] using this
    · simp
  · rw [if_neg (fun h => hS h.2)]
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro i _
    have hsp := sum_split u
    by_cases h1 : (∑ j, upper u j) = i.val + 1
    · rw [if_pos h1, one_mul, if_neg, mul_zero]
      rintro ⟨-, h2⟩
      have := i.isLt
      omega
    · rw [if_neg h1, zero_mul, mul_zero]

/-- `(e_m, h_v) = [every vⱼ ≤ 1 and |v| = m]` at `q = 1`, for every sequence `v`. -/
theorem form_eOne_vWord (m : ℕ) {c : ℕ} (v : Fin c → ℕ) :
    form (1 : k) (eOne k m) (vWord k v) =
      if (∀ j, v j ≤ 1) ∧ (∑ j, v j) = m then 1 else 0 := by
  induction m using Nat.strong_induction_on generalizing c with
  | _ m ih =>
    cases m with
    | zero =>
      rw [eOne_zero, ← h_zero k, form_h_vWord]
      by_cases hs : (∑ j, v j) = 0
      · rw [if_pos hs, if_pos ⟨fun j => by
          have := (sum_eq_zero_iff_all v).mp hs j; omega, hs⟩]
      · rw [if_neg hs, if_neg (fun h => hs h.2)]
    | succ m =>
      rw [eOne_succ, map_sum, LinearMap.sum_apply]
      have hterm : ∀ i : Fin (m + 1),
          form (1 : k) (((-1 : k) ^ i.val) • (h k (i.val + 1) * eOne k (m - i.val))) (vWord k v) =
          (-1 : k) ^ i.val * ∑ u : Splits v,
            ((if (∑ j, upper u j) = i.val + 1 then 1 else 0) *
              if (∀ j, lower u j ≤ 1) ∧ (∑ j, lower u j) = m - i.val then 1 else 0) := by
        intro i
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← adjointness, coproduct_vWord,
          map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        rw [one_pow, one_smul, tensorForm_tmul, form_h_vWord, ih (m - i.val) (by omega)]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), eOne_comb]

/-! ## Products of elementary functions against products of complete ones -/

/-- Number of `0/1` matrices with row sums `ρ` and column sums `β`, as an element of `k`. -/
def zo {r c : ℕ} (ρ : Fin r → ℕ) (β : Fin c → ℕ) : k :=
  ∑ M : Mat ρ β, ∏ i, ∏ j, if M i j ≤ 1 then 1 else 0

theorem zo_summand {r c : ℕ} {ρ : Fin r → ℕ} {β : Fin c → ℕ} (M : Mat ρ β) :
    (∏ i, ∏ j, if M i j ≤ 1 then (1 : k) else 0) = if ∀ i j, M i j ≤ 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one (fun i _ => Finset.prod_eq_one (fun j _ => if_pos (h i j)))
  · push_neg at h
    obtain ⟨i, j, hij⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (by omega)))

theorem zo_eq_card {r c : ℕ} (ρ : Fin r → ℕ) (β : Fin c → ℕ) :
    zo (k := k) ρ β = Fintype.card {M : Mat ρ β // ∀ i j, M i j ≤ 1} := by
  unfold zo
  rw [Finset.sum_congr rfl (fun M _ => zo_summand M), Finset.sum_boole, Fintype.card_subtype]

theorem zo_single_row {c : ℕ} (a : ℕ) (w : Fin c → ℕ) :
    zo (k := k) (fun _ : Fin 1 => a) w = if (∀ j, w j ≤ 1) ∧ (∑ j, w j) = a then 1 else 0 := by
  unfold zo
  simp only [zo_summand]
  by_cases hs : (∑ j, w j) = a
  · let Z : Mat (fun _ : Fin 1 => a) w :=
      ⟨fun _ j => w j, by constructor <;> funext i <;> simp [rowSum, colSum, hs]⟩
    have hz (M : Mat (fun _ : Fin 1 => a) w) : M = Z := by
      apply Subtype.ext; funext i j
      have h := congrFun M.property.2 j
      simpa [colSum, Subsingleton.elim i 0] using h
    rw [Finset.sum_eq_single Z]
    · by_cases hw : ∀ j, w j ≤ 1
      · rw [if_pos (fun _ => hw), if_pos ⟨hw, hs⟩]
      · rw [if_neg (fun h => hw (h ⟨0, Nat.one_pos⟩)), if_neg (fun h => hw h.1)]
    · intro M _ h; exact (h (hz M)).elim
    · simp
  · rw [if_neg (fun h => hs h.2)]
    apply Finset.sum_eq_zero
    intro M _
    exfalso
    apply hs
    have := total_eq M
    simpa using this.symm

theorem zo_convolution {r s c : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    zo (k := k) (Fin.addCases β γ) α = ∑ u : Splits α, zo β (upper u) * zo γ (lower u) := by
  unfold zo
  rw [← (matrixEquivSplit β γ α).symm.sum_comp]
  change (∑ z : SplitMatrices β γ α,
    ∏ i, ∏ j, if (joinMat z : Raw (r + s) c) i j ≤ 1 then (1 : k) else 0) = _
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro U _
  apply Finset.sum_congr rfl; intro V _
  rw [Fin.prod_univ_add]
  simp only [joinMat, join_left, join_right]

variable (k) in
/-- `e_ρ = e_{ρ₁} ⋯ e_{ρ_r}` at `q = 1`. -/
def eWordV {r : ℕ} (ρ : Fin r → ℕ) : L k := (List.ofFn fun i => eOne k (ρ i)).prod

theorem eWordV_join {r s : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) :
    eWordV k (Fin.addCases β γ) = eWordV k β * eWordV k γ := by
  unfold eWordV
  rw [List.ofFn_add, List.prod_append]
  simp

theorem eWordV_single (a : ℕ) : eWordV k (fun _ : Fin 1 => a) = eOne k a := by
  simp [eWordV]

theorem form_eWordV_join {r s c : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    form (1 : k) (eWordV k (Fin.addCases β γ)) (vWord k α) =
      ∑ u : Splits α, form (1 : k) (eWordV k β) (vWord k (upper u)) *
        form (1 : k) (eWordV k γ) (vWord k (lower u)) := by
  rw [eWordV_join, ← adjointness, coproduct_vWord, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [one_pow, one_smul, tensorForm_tmul]

/-- `(e_ρ, h_β)` at `q = 1` is the number of `0/1` matrices with row sums `ρ`, column sums `β`. -/
theorem form_eWordV_vWord {r c : ℕ} (ρ : Fin r → ℕ) (β : Fin c → ℕ) :
    form (1 : k) (eWordV k ρ) (vWord k β) = zo ρ β := by
  induction r generalizing c with
  | zero =>
    have h1 : eWordV k ρ = h k 0 := by simp [eWordV]
    rw [h1, form_h_vWord, zo_eq_card]
    by_cases hs : (∑ j, β j) = 0
    · rw [if_pos hs]
      have hb : ∀ j, β j = 0 := (sum_eq_zero_iff_all β).mp hs
      let Z : Mat ρ β := ⟨fun i => Fin.elim0 i, funext fun i => Fin.elim0 i, by
        funext j; simp [colSum, hb j]⟩
      have : Unique {M : Mat ρ β // ∀ i j, M i j ≤ 1} :=
        { default := ⟨Z, fun i => Fin.elim0 i⟩
          uniq := fun M => Subtype.ext (Subtype.ext (funext fun i => Fin.elim0 i)) }
      rw [Fintype.card_unique]; simp
    · rw [if_neg hs]
      have : IsEmpty {M : Mat ρ β // ∀ i j, M i j ≤ 1} :=
        ⟨fun M => hs (by have := total_eq M.val; simp at this; omega)⟩
      rw [Fintype.card_eq_zero]; simp
  | succ r ih =>
    have hρ : ρ = Fin.addCases (Fin.init ρ) (fun _ : Fin 1 => ρ (Fin.last r)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have : Fin.last r = Fin.natAdd r (0 : Fin 1) := rfl
        rw [this, Fin.addCases_right]
      · have : Fin.castSucc j = Fin.castAdd 1 j := rfl
        rw [this, Fin.addCases_left]; rfl
    rw [hρ, form_eWordV_join, zo_convolution]
    apply Finset.sum_congr rfl
    intro u _
    rw [ih, eWordV_single, form_eOne_vWord, zo_single_row]

/-! ## Partitions -/

open EKSemiorthogonality (rows)

variable (k) in
/-- `e_λ` for a list of parts. -/
def eWordL (l : List ℕ) : L k := (l.map (eOne k)).prod

theorem eWordL_rows (μ : YoungDiagram) : eWordL k μ.rowLens = eWordV k (rows μ) := by
  rw [eWordL, eWordV, EKSemiorthogonality.rowLens_eq_ofFn, List.map_ofFn]
  rfl

theorem hWord_rows (μ : YoungDiagram) : hWord k μ.rowLens = vWord k (rows μ) := by
  rw [vWord, ← EKSemiorthogonality.rowLens_eq_ofFn]

/-- `(e_ν, h_μ) = #{0/1 matrices, row sums ν, column sums μ}` at `q = 1`. -/
theorem form_eWord_hWord (ν μ : YoungDiagram) :
    form (1 : k) (eWordL k ν.rowLens) (hWord k μ.rowLens) =
      Fintype.card (EKDualBases.ZeroOneMatrices ν μ) := by
  rw [eWordL_rows, hWord_rows, form_eWordV_vWord, zo_eq_card]
  rfl

/-- Vanishing: `(h_λ, e_{μᵀ}) ≠ 0` forces `λ ⊴ μ` (Gale–Ryser necessity). -/
theorem dom_of_form_ne_zero (lam μ : YoungDiagram)
    (h : form (1 : k) (hWord k lam.rowLens) (eWordL k μ.transpose.rowLens) ≠ 0) :
    EKProp310.Dom lam μ := by
  rw [form_symm, form_eWord_hWord] at h
  have hne : Nonempty (EKDualBases.ZeroOneMatrices μ.transpose lam) := by
    by_contra he
    rw [not_nonempty_iff] at he
    exact h (by simp)
  obtain ⟨A⟩ := hne
  have hd := EKLemma311Cond.gale_ryser μ.transpose lam A
  rw [YoungDiagram.transpose_transpose] at hd
  exact hd

/-- Diagonal: exactly one `0/1` matrix with row sums `λᵀ` and column sums `λ`. -/
theorem card_zeroOne_diag (lam : YoungDiagram) :
    Fintype.card (EKDualBases.ZeroOneMatrices lam.transpose lam) = 1 := by
  classical
  -- transpose to row sums `λ`
  let T : EKDualBases.ZeroOneMatrices lam.transpose lam ≃
      {M : Mat (rows lam) (rows lam.transpose) // ∀ i j, M i j ≤ 1} :=
    { toFun := fun M => ⟨(transposeEquiv _ _) M.val, fun i j => M.property j i⟩
      invFun := fun M => ⟨(transposeEquiv _ _) M.val, fun i j => M.property j i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr T]
  -- the column margins are the Ferrers margins
  have key : ∀ (n : ℕ) (hn : n = lam.rowLen 0) (α : Fin n → ℕ),
      (∀ j : Fin n, α j = lam.colLen j.val) →
      Fintype.card {M : Mat (rows lam) α // ∀ i j, M i j ≤ 1} = 1 := by
    intro n hn α hα
    subst hn
    have he : α = colSum (EKSemiorthogonality.ferrers (rows lam) (lam.rowLen 0)) := by
      funext j
      rw [hα, EKSemiorthogonality.ferrers_colSum]
    subst he
    have hb : ∀ i, rows lam i ≤ lam.rowLen 0 :=
      fun i => lam.rowLen_anti 0 i.val (Nat.zero_le _)
    let F := EKSemiorthogonality.ferrersMixed (rows lam) (lam.rowLen 0) hb
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨F.val, fun i j => F.property i j (by simp)⟩, ?_⟩
    intro M
    apply Subtype.ext
    apply Subtype.ext
    exact EKSemiorthogonality.ferrers_unique M.val M.property
  have hlen : lam.transpose.colLen 0 = lam.rowLen 0 := by
    rw [YoungDiagram.colLen_transpose]
  exact key _ hlen (rows lam.transpose) (fun j => by
    simp only [rows, YoungDiagram.rowLen_transpose])

theorem form_diag (lam : YoungDiagram) :
    form (1 : k) (hWord k lam.rowLens) (eWordL k lam.transpose.rowLens) = 1 := by
  rw [form_symm, form_eWord_hWord, card_zeroOne_diag, Nat.cast_one]

/-- The matrix `A_{λμ} = (h_λ, e_{μᵀ})` at `q = 1` on partitions of `n`. -/
def unitriMatrix (n : ℕ) : Matrix (DegreeShape n) (DegreeShape n) k :=
  Matrix.of fun lam μ => form (1 : k) (hWord k lam.val.rowLens) (eWordL k μ.val.transpose.rowLens)

/-- EK p.9, `q = 1`: for every linear order on partitions of `n` refining dominance, the matrix
of the form in the bases `{h_λ}`, `{e_{λᵀ}}` is upper triangular with ones on the diagonal
(any commutative ring `k`). -/
theorem ek_q1_unitriangular (n : ℕ) [LinearOrder (DegreeShape n)]
    (hrefine : ∀ lam μ : DegreeShape n, EKProp310.Dom lam.val μ.val → lam ≤ μ) :
    (unitriMatrix (k := k) n).BlockTriangular id ∧ ∀ lam, unitriMatrix (k := k) n lam lam = 1 := by
  refine ⟨?_, fun lam => form_diag lam.val⟩
  intro lam μ hlt
  by_contra hne
  exact absurd (hrefine lam μ (dom_of_form_ne_zero lam.val μ.val hne)) (not_le.mpr hlt)

theorem ek_q1_det (n : ℕ) [LinearOrder (DegreeShape n)]
    (hrefine : ∀ lam μ : DegreeShape n, EKProp310.Dom lam.val μ.val → lam ≤ μ) :
    (unitriMatrix (k := k) n).det = 1 := by
  obtain ⟨ht, hd⟩ := ek_q1_unitriangular (k := k) n hrefine
  rw [Matrix.det_of_upperTriangular ht]
  exact Finset.prod_eq_one (fun lam _ => hd lam)

end OddMath.Frontier.EKGeneralQ

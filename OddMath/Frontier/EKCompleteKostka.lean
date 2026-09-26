import OddMath.Frontier.EKCompleteLemma215
import OddMath.Frontier.EKAutomorphismsControls

/-!
# [EK] Finite-range claims extended to all degrees

Source: Ellis–Khovanov, arXiv:1107.5610v2.
* §3.3, p. 27, after (3.7): "`K_{(n)μ} = 1` for all `μ ⊢ n`, `K_{(1ⁿ)μ} = δ_{μ,(1ⁿ)}`".
  Proved for every `n` (`kostka_row`, `kostka_column`, `kostka_column_replicate`).
* §2.3, p. 19: "`ψ₃(e_n) ≠ e_n` for `n > 1`". Proved for every `n`, with the exact
  set: `ψ₃(e_n) = e_n ↔ n ≤ 1` (`psi3_e_fixed_iff`).

Routes.
* `K_{(n)μ}`: `s_{(n)} = h_n` (nothing strictly dominates `(n)`), `(h_n, h_μ) = 1`
  (EK Prop 3.1, one-row matrices), and Cor 3.9. `K_{(1ⁿ)μ}`: `K_{λμ} ≠ 0` forces `μ ⊴ λ`,
  and `(1ⁿ)` is dominated by every partition of `n`.
* `ψ₃(e_n)`: the character `χ : Λ → ℤ`, `h_k ↦ 1`, satisfies `χ(e_n) = 0` for `n ≥ 2`
  (apply `χ` to (2.5)) and `χ(ψ₃(e_n)) = 2` for `n ≥ 2` (apply `χ ∘ ψ₃` to (2.5), use
  `ψ₃(xy) = (−1)^{|x||y|} ψ₃(y)ψ₃(x)`, and solve the resulting convolution identity with
  power series: `F(t)(1 − t) = 1 + t²`).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKComplete
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition ePartition)

local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## `K_{(n)μ} = 1` -/

theorem pi_hWord' (α : List ℕ) :
    pi (CompleteElementary.hWord α) = (α.map EKElementaryQuotient.h).prod := by
  simp only [CompleteElementary.hWord, map_list_prod, List.map_map]
  rfl

/-- `(h_n, h_μ) = 1` for `|μ| = n` (EK Prop 3.1: a single one-row matrix, no crossings). -/
theorem pair_h_hPartition (μ : YoungDiagram) :
    quotientPairing (EKElementaryQuotient.h μ.card) (hPartition μ) = 1 := by
  have hs : (∑ j, μ.rowLens.get j) = μ.card := by
    rw [← List.sum_ofFn, List.ofFn_get, rowLens_sum]
  have h1 := EKPairingMatrices.pairing_single_row μ.rowLens.get
  rw [hs, ← EKPairingAdjoint.pairing_vWord, EKPairingAdjoint.vWord_singleton] at h1
  have hv : EKPairingAdjoint.vWord μ.rowLens.get = CompleteElementary.hWord μ.rowLens := by
    simp only [EKPairingAdjoint.vWord, List.ofFn_get]
  rw [hv] at h1
  rw [EKElementaryQuotient.h, EKPartitionSpanning.hPartition, ← pi_hWord', quotientPairing_pi]
  exact h1

theorem hPartition_row {n : ℕ} {lam : YoungDiagram} (hl : lam.rowLens = [n]) :
    hPartition lam = EKElementaryQuotient.h n := by
  simp [EKPartitionSpanning.hPartition, hl]

theorem card_of_rowLens {n : ℕ} {lam : YoungDiagram} (hl : lam.rowLens = [n]) : lam.card = n := by
  rw [← rowLens_sum, hl]; simp

/-- `s_{(n)} = h_n`. -/
theorem schur_row {n : ℕ} (lam : DegreeShape n) (hl : lam.val.rowLens = [n]) :
    (EKSchurOrthonormal.schur n lam : Q) = EKElementaryQuotient.h n := by
  have h1 := EKProp310.schur_sub_mem_upS n lam
  have hbot : EKProp310.UpS n lam = ⊥ := by
    rw [EKProp310.UpS, Submodule.span_eq_bot]
    rintro _ ⟨ν, ⟨hdom, hne⟩, rfl⟩
    have h2 := EKProp310.dom_row lam.val hl ν lam.property
    exact absurd (Subtype.ext (EKProp310.dom_antisymm h2 hdom)) hne
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
  rw [← hPartition_row hl, ← degreeHBasis_apply]
  exact congrArg Subtype.val h1

/-- **EK p. 27: `K_{(n)μ} = 1` for every `μ ⊢ n`, every `n`.** -/
theorem kostka_row {n : ℕ} (lam μ : YoungDiagram) (hl : lam.rowLens = [n]) (hμ : μ.card = n) :
    signedKostka lam μ = 1 := by
  set L : DegreeShape n := ⟨lam, card_of_rowLens hl⟩
  set M : DegreeShape n := ⟨μ, hμ⟩
  have hs := schur_row L hl
  have hε : quotientPairing (EKSchurOrthonormal.schur n L : Q) (EKSchurOrthonormal.schur n L : Q)
      = 1 := by
    rw [hs, EKElementaryQuotient.h, quotientPairing_pi, EKPairingAdjoint.pairing_h_self]
  have hK : quotientPairing (EKSchurOrthonormal.schur n L : Q) (hPartition μ) =
      signedKostka lam μ := by
    have hd := EKSchurOrthonormal.schur_defining n M
    rw [show hPartition μ = ((degreeHBasis n M : degreePiece n) : Q) from
      (degreeHBasis_apply n M).symm, hd, Submodule.coe_sum, map_sum,
      Finset.sum_eq_single L]
    · rw [Submodule.coe_smul, map_zsmul, hε, smul_eq_mul, mul_one]
    · intro κ _ hκ
      rw [Submodule.coe_smul, map_zsmul, EKClosureComposition.corollary_3_9, if_neg (Ne.symm hκ),
        smul_zero]
    · intro h; exact absurd (Finset.mem_univ L) h
  rw [← hK, hs, ← hμ]
  exact pair_h_hPartition μ

/-! ## `K_{(1ⁿ)μ} = δ_{μ,(1ⁿ)}` -/

/-- **EK p. 27: `K_{(1ⁿ)μ} = δ_{μ,(1ⁿ)}`, every `n`.** Here `(1ⁿ)` is given by `λᵀ = (n)`. -/
theorem kostka_column {n : ℕ} (lam μ : DegreeShape n) (hl : lam.val.transpose.rowLens = [n]) :
    signedKostka lam.val μ.val = if μ = lam then 1 else 0 := by
  split_ifs with h
  · rw [h, signedKostka_diag]
  · by_contra hK
    have h1 : EKProp310.Dom μ.val lam.val := EKProp310.dom_of_kostka_ne_zero hK
    have h2 : EKProp310.Dom μ.val.transpose lam.val.transpose :=
      EKProp310.dom_row lam.val.transpose hl (transposeShape n μ) (transposeShape n lam).property
    have hc : μ.val.transpose.card = lam.val.transpose.card :=
      (transposeShape n μ).property.trans (transposeShape n lam).property.symm
    have h3 := EKProp310.dom_transpose hc h2
    simp only [YoungDiagram.transpose_transpose] at h3
    exact h (Subtype.ext (EKProp310.dom_antisymm h1 h3))

/-- `λ = (1ⁿ)` in row form gives `λᵀ = (n)`. -/
theorem transpose_rowLens_of_replicate {n : ℕ} (hn : 0 < n) {lam : YoungDiagram}
    (hl : lam.rowLens = List.replicate n 1) : lam.transpose.rowLens = [n] := by
  have hc : lam.colLen 0 = n := by
    rw [← YoungDiagram.length_rowLens, hl, List.length_replicate]
  have hr : lam.rowLen 0 = 1 := by
    have h0 : 0 < lam.rowLens.length := by rw [hl, List.length_replicate]; exact hn
    have := YoungDiagram.get_rowLens (μ := lam) (i := 0) (h := h0)
    rw [← this]
    simp [hl, List.getElem_replicate]
  unfold YoungDiagram.rowLens
  rw [YoungDiagram.colLen_transpose, hr]
  simp [List.range_succ, YoungDiagram.rowLen_transpose, hc]

/-- `K_{(1ⁿ)μ} = δ_{μ,(1ⁿ)}` with `(1ⁿ)` given by its row lengths. -/
theorem kostka_column_replicate {n : ℕ} (hn : 0 < n) (lam μ : DegreeShape n)
    (hl : lam.val.rowLens = List.replicate n 1) :
    signedKostka lam.val μ.val = if μ = lam then 1 else 0 :=
  kostka_column lam μ (transpose_rowLens_of_replicate hn hl)

/-! ## The character `χ` and `ψ₃(e_n)` -/

open EKAutomorphisms (s psi3)
open EKElementaryQuotient (e h)

/-- The character `χ : Λ → ℤ`, `h_k ↦ 1` (it respects (2.11)–(2.12)). -/
def chi : Q →+* ℤ :=
  EKAutomorphisms.descend (fun _ => (1 : ℤ)) rfl (fun _ _ _ => rfl)
    (fun _ _ _ => by simp [add_comm])

@[simp] theorem chi_h (n : ℕ) : chi (h n) = 1 :=
  EKAutomorphisms.descend_h _ _ _ _ n

theorem e_mem (n : ℕ) : e n ∈ degreePiece n := by
  rw [degreePiece_eq_hPartition_span]; exact elementary_mem_hPiece n

theorem h_mem (n : ℕ) : h n ∈ degreePiece n := by
  have := EKAutomorphisms.hWord_degree [n]
  simpa using this

/-- (2.5) in `Λ`, for `n ≥ 1`: `Σ_k (−1)^{C(k+1,2)} e_k h_{n−k} = 0`. -/
theorem relation_2_5 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), s k • (e k * h (n - k)) = 0 := by
  have h1 := congrArg pi (CompleteElementary.elementary_complete_inverse_range n hn)
  rw [map_sum, map_zero] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, s, zsmul_eq_mul]
  simp [e, h, mul_assoc]

theorem s_isUnit (n : ℕ) : s n = 1 ∨ s n = -1 := neg_one_pow_eq_or ℤ _

theorem s_ne_zero (n : ℕ) : s n ≠ 0 := by
  rcases s_isUnit n with h | h <;> rw [h] <;> decide

theorem s_add_two (n : ℕ) : s (n + 2) = - s n := by
  rw [EKAutomorphisms.s_succ, EKAutomorphisms.s_succ, ← mul_assoc, ← pow_add]
  have h : (-1 : ℤ) ^ (n + 1 + 1 + (n + 1)) = -1 := by
    rw [show n + 1 + 1 + (n + 1) = 2 * (n + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h]; ring

/-- `χ(e_n) = 1` for `n ≤ 1` and `0` for `n ≥ 2`. -/
theorem chi_e (n : ℕ) : chi (e n) = if n ≤ 1 then 1 else 0 := by
  have hrel (m : ℕ) (hm : 0 < m) : ∑ k ∈ Finset.range (m + 1), s k * chi (e k) = 0 := by
    have := congrArg chi (relation_2_5 m hm)
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, map_mul, chi_h, mul_one, smul_eq_mul]
  have he0 : chi (e 0) = 1 := by
    rw [e, CompleteElementary.elementary_zero, map_one, map_one]
  have he1 : chi (e 1) = 1 := by
    rw [EKPresentationControls.degree_one, chi_h]
  match n with
  | 0 => simpa using he0
  | 1 => simpa using he1
  | m + 2 =>
    have h2 := hrel (m + 2) (by omega)
    have h1 := hrel (m + 1) (by omega)
    rw [Finset.sum_range_succ, h1, zero_add] at h2
    rw [if_neg (by omega)]
    exact (mul_eq_zero.mp h2).resolve_left (s_ne_zero _)

/-- `f_n = χ(ψ₃(e_n))`. -/
def fpsi (n : ℕ) : ℤ := chi (psi3 (e n))

/-- `χ ∘ ψ₃` applied to (2.5): `Σ_k (−1)^{C(n−k+1,2)} χ(ψ₃ e_k) = 0` for `n ≥ 1`. -/
theorem fpsi_rel (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), fpsi k * s (n - k) = 0 := by
  have h1 := congrArg (fun x => chi (psi3 x)) (relation_2_5 n hn)
  simp only [map_sum, map_zero, map_zsmul] at h1
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      s k • chi (psi3 (e k * h (n - k))) = s n * (fpsi k * s (n - k)) := by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [EKAutomorphisms.psi3_mul (e_mem k) (h_mem (n - k)), map_zsmul, map_mul,
      EKAutomorphisms.psi3_h, chi_h, one_mul, smul_eq_mul, smul_eq_mul, fpsi]
    have hs := EKAutomorphisms.s_add k (n - k)
    rw [Nat.add_sub_cancel' hk'] at hs
    rw [hs]
    have h2 : s k * s k = 1 := EKAutomorphisms.s_square k
    have h3 : s (n - k) * s (n - k) = 1 := EKAutomorphisms.s_square (n - k)
    linear_combination (-(s k * (-1 : ℤ) ^ (k * (n - k)) * chi (psi3 (e k)))) * h3
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h1
  exact (mul_eq_zero.mp h1).resolve_left (s_ne_zero n)

theorem fpsi_zero : fpsi 0 = 1 := by
  rw [fpsi, e, CompleteElementary.elementary_zero, map_one]
  have : psi3 (1 : Q) = 1 := by
    have := EKAutomorphisms.psi3_h 0
    rwa [h, CompleteElementary.h_zero, map_one] at this
  rw [this, map_one]

/-- `χ(ψ₃(e_n)) = 2` for `n ≥ 2` (and `= 1` for `n ≤ 1`). -/
theorem fpsi_eq (n : ℕ) : fpsi n = if n ≤ 1 then 1 else 2 := by
  let V : PowerSeries ℤ := PowerSeries.mk fpsi
  let S : PowerSeries ℤ := PowerSeries.mk s
  have hVS : V * S = 1 := by
    ext m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [V, S, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [fpsi_zero]
    · rw [if_neg (by omega)]
      exact fpsi_rel m hm
  have hS : S * (1 + PowerSeries.X ^ 2) = 1 - PowerSeries.X := by
    ext m
    rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow', map_sub,
      PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp only [S, PowerSeries.coeff_mk]
    match m with
    | 0 => simp
    | 1 => simp [s]
    | m + 2 =>
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel,
        s_add_two]
      ring
  have hV : V * (1 - PowerSeries.X) = 1 + PowerSeries.X ^ 2 := by
    rw [← hS, ← mul_assoc, hVS, one_mul]
  have hstep (m : ℕ) : fpsi (m + 1) - fpsi m = if m + 1 = 2 then 1 else 0 := by
    have := congrArg (PowerSeries.coeff ℤ (m + 1)) hV
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X, map_add,
      PowerSeries.coeff_one, PowerSeries.coeff_X_pow] at this
    simpa [V] using this
  have h1 : fpsi 1 = 1 := by have := hstep 0; simp [fpsi_zero] at this; linarith
  have h2 : fpsi 2 = 2 := by have := hstep 1; simp [h1] at this; linarith
  have hge : ∀ m, fpsi (m + 2) = 2 := by
    intro m
    induction m with
    | zero => exact h2
    | succ m ih =>
      have := hstep (m + 2)
      rw [if_neg (by omega), ih] at this
      rw [show m + 1 + 2 = m + 2 + 1 by ring]
      linarith
  match n with
  | 0 => simp [fpsi_zero]
  | 1 => simp [h1]
  | m + 2 => rw [hge m, if_neg (by omega)]

/-- **EK p. 19: `ψ₃(e_n) ≠ e_n` for every `n ≥ 2`.** -/
theorem psi3_e_ne (n : ℕ) (hn : 2 ≤ n) : psi3 (e n) ≠ e n := by
  intro heq
  have h1 := fpsi_eq n
  rw [fpsi, heq, chi_e, if_neg (by omega), if_neg (by omega)] at h1
  exact absurd h1 (by decide)

/-- The exact set: `ψ₃(e_n) = e_n ↔ n ≤ 1`. -/
theorem psi3_e_fixed_iff (n : ℕ) : psi3 (e n) = e n ↔ n ≤ 1 := by
  refine ⟨fun h => by_contra fun hn => psi3_e_ne n (by omega) h, fun hn => ?_⟩
  match n, hn with
  | 0, _ =>
    rw [e, CompleteElementary.elementary_zero, map_one]
    have := EKAutomorphisms.psi3_h 0
    rwa [h, CompleteElementary.h_zero, map_one] at this
  | 1, _ => rw [EKPresentationControls.degree_one, EKAutomorphisms.psi3_h]

end OddMath.Frontier.EKComplete

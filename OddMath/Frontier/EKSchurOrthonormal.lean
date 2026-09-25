import OddMath.Frontier.EKSchurOrthonormalControls

/-!
# EK1107.5610v2 §3.3: Corollaries 3.8 and 3.9 from identity (3.9), degreewise

Source: printed p27 (3.6), (3.7); printed p28 (3.9), Corollary 3.8 (3.10) and proof,
Corollary 3.9 (3.11) and proof (frozen source excerpt PAGE 27–29).

* `schur d λ` is the source s_λ, defined INSIDE the actual homogeneous piece
  `degreePiece d ⊆ Q` as the unique solution of (3.6) `h_μ = Σ_λ K_{λμ} s_λ`, where
  `K = TableauDominance.signedKostka` is the literal odd Kostka number (3.7) and uniqueness
  is the existing `KostkaModuleInversion`/`SignedKostkaInvertibility` inversion.
* `Identity39 d` is EXACTLY (3.9) in the single degree d, with the source M′ = (h,h)
  (`EKDualBases.Mh`, not the (e,h) matrix `EKDualBases.M`) and the sign
  `(-1)^{λ₂+λ₄+…}`.  It is a hypothesis of the general theorems; nothing stronger is assumed.
* `corollary_3_8`: (3.10) `(-1)^{C(λᵀ,2)} s_λ = Σ_μ K_{λμ} m_μ`, `m = EKDualBases.mBasis d`.
* `corollary_3_9`: (3.11) `(s_λ, s_μ) = (-1)^{C(λᵀ,2)} δ_{λμ}` in the actual pairing.
* `sign_bridge`: `(-1)^{C(λᵀ,2)} = (-1)^{λ₂+λ₄+…}` for EVERY Young diagram (the source's
  second equality in (3.9)), proved, not assumed.
* `identity39_le_four`: the hypothesis is DISCHARGED for d ≤ 4 by the exact computations
  in `EKSchurOrthonormalControls` (proved evaluation bridges + `decide`), giving the
  unconditional `corollary_3_8_le_four` / `corollary_3_9_le_four`.

No Gram–Schmidt, no positive-definiteness, no Lemma 2.15 / Prop 3.10 route, and no proof
of (3.9) for general d.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKSchurOrthonormal
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition)
open EKSchurOrthonormalControls (evenParts transposeChoose)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## The two source forms of the sign agree for every diagram -/

private theorem list_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem transposeChoose_eq (μ : YoungDiagram) :
    transposeChoose μ = ∑ j ∈ Finset.range (μ.rowLen 0), (μ.colLen j).choose 2 := by
  unfold transposeChoose YoungDiagram.rowLens
  rw [List.map_map, YoungDiagram.colLen_transpose]
  rw [show ((fun a => a.choose 2) ∘ μ.transpose.rowLen) = fun j => (μ.colLen j).choose 2 from
    funext fun j => by simp [YoungDiagram.rowLen_transpose]]
  exact list_sum_range _ _

/-- Pairs of cells in a common column, counted column by column. -/
theorem cells_fst_sum_cols (μ : YoungDiagram) :
    ∑ p ∈ μ.cells, p.1 = ∑ j ∈ Finset.range (μ.rowLen 0), (μ.colLen j).choose 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := Finset.range (μ.rowLen 0))]
  · apply Finset.sum_congr rfl
    intro j _
    have hc : μ.cells.filter (fun p => p.2 = j) = Finset.range (μ.colLen j) ×ˢ {j} :=
      YoungDiagram.col_eq_prod
    rw [hc, Finset.sum_product, Nat.choose_two_right, ← Finset.sum_range_id]
    simp
  · rintro ⟨i, j⟩ hp
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
    exact μ.up_left_mem (Nat.zero_le i) le_rfl ((YoungDiagram.mem_cells _).1 hp)

/-- The same count, row by row: the cell in row i has i cells above it. -/
theorem cells_fst_sum_rows (μ : YoungDiagram) :
    ∑ p ∈ μ.cells, p.1 = ∑ i ∈ Finset.range (μ.colLen 0), i * μ.rowLen i := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.range (μ.colLen 0))]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (fun p hp => (Finset.mem_filter.1 hp).2), Finset.sum_const,
      smul_eq_mul, YoungDiagram.rowLen_eq_card, mul_comm]
    rfl
  · rintro ⟨i, j⟩ hp
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen]
    exact μ.up_left_mem le_rfl (Nat.zero_le j) ((YoungDiagram.mem_cells _).1 hp)

theorem evenParts_rowLens (μ : YoungDiagram) :
    evenParts μ.rowLens =
      ∑ i ∈ Finset.range (μ.colLen 0), if i % 2 = 1 then μ.rowLen i else 0 := by
  unfold evenParts
  rw [YoungDiagram.length_rowLens]
  apply Finset.sum_congr rfl
  intro i hi
  have hl : i < μ.rowLens.length := by
    rw [YoungDiagram.length_rowLens]; exact Finset.mem_range.1 hi
  have hi' := Finset.mem_range.1 hi
  simp [YoungDiagram.rowLens, hi']

private theorem parity (n : ℕ) (f : ℕ → ℕ) :
    (-1 : ℤ) ^ (∑ i ∈ Finset.range n, i * f i) =
      (-1 : ℤ) ^ (∑ i ∈ Finset.range n, if i % 2 = 1 then f i else 0) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_mul]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [if_neg (by omega), (Nat.even_iff.2 h).neg_one_pow, one_pow, pow_zero]
  · rw [if_pos h, (Nat.odd_iff.2 h).neg_one_pow]

/-- Source (3.9), second equality: `(-1)^{C(λᵀ,2)} = (-1)^{λ₂+λ₄+λ₆+…}`, all λ. -/
theorem sign_bridge (μ : YoungDiagram) :
    (-1 : ℤ) ^ transposeChoose μ = (-1 : ℤ) ^ evenParts μ.rowLens := by
  rw [transposeChoose_eq, ← cells_fst_sum_cols, cells_fst_sum_rows, parity, evenParts_rowLens]

theorem sign_mul_self (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-! ## The source s_λ via (3.6), inside the actual degree-d piece -/

/-- s_λ: the unique solution of (3.6) `h_μ = Σ_λ K_{λμ} s_λ` in `degreePiece d`. -/
def schur (d : ℕ) : DegreeShape d → degreePiece d :=
  KostkaModuleInversion.recover d (degreeHBasis d)

/-- (3.6), literally. -/
theorem schur_defining (d : ℕ) (μ : DegreeShape d) :
    degreeHBasis d μ = ∑ lam, signedKostka lam.val μ.val • schur d lam :=
  (congrFun (KostkaModuleInversion.rightInverse d (⇑(degreeHBasis d))) μ).symm

/-- (3.6) determines s uniquely, even when tested only in `Q`. -/
theorem schur_val_unique (d : ℕ) (S : DegreeShape d → Q)
    (hS : ∀ μ : DegreeShape d, hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • S lam) (lam : DegreeShape d) :
    (schur d lam : Q) = S lam := by
  have h1 : KostkaModuleInversion.transform d (fun l => (schur d l : Q)) =
      fun μ => hPartition μ.val := by
    funext μ
    have h := congrArg Subtype.val (schur_defining d μ)
    rw [degreeHBasis_apply] at h
    rw [h, Submodule.coe_sum]
    rfl
  have h2 : KostkaModuleInversion.transform d S = fun μ => hPartition μ.val := by
    funext μ
    exact (hS μ).symm
  have h := congrFun ((KostkaModuleInversion.uniqueSolution d (fun μ => hPartition μ.val)).unique
    h1 h2) lam
  exact h

/-- Exactly (3.9) in the single degree d (source M′ = (h,h)), and nothing stronger. -/
def Identity39 (d : ℕ) : Prop :=
  ∀ μ ρ : DegreeShape d, Mh d μ ρ = ∑ lam : DegreeShape d,
    (-1 : ℤ) ^ evenParts lam.val.rowLens * signedKostka lam.val μ.val * signedKostka lam.val ρ.val

/-- Corollary 3.8, (3.10): `(-1)^{C(λᵀ,2)} s_λ = Σ_μ K_{λμ} m_μ`, assuming (3.9) in degree d. -/
theorem corollary_3_8 (d : ℕ) (h39 : Identity39 d) (lam : DegreeShape d) :
    (-1 : ℤ) ^ transposeChoose lam.val • schur d lam =
      ∑ μ, signedKostka lam.val μ.val • mBasis d μ := by
  let t : DegreeShape d → degreePiece d := fun l => ∑ μ, signedKostka l.val μ.val • mBasis d μ
  let ε : DegreeShape d → ℤ := fun l => (-1 : ℤ) ^ evenParts l.val.rowLens
  have hT : KostkaModuleInversion.transform d (fun l => ε l • t l) = ⇑(degreeHBasis d) := by
    funext ρ
    change ∑ l, signedKostka l.val ρ.val • (ε l • t l) = degreeHBasis d ρ
    rw [h_eq_Mh_m]
    simp only [t, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro μ _
    rw [← Finset.sum_smul, h39 ρ μ]
    have hsum : ∑ l : DegreeShape d, signedKostka l.val ρ.val * (ε l * signedKostka l.val μ.val) =
        ∑ l : DegreeShape d, (-1 : ℤ) ^ evenParts l.val.rowLens * signedKostka l.val ρ.val *
          signedKostka l.val μ.val :=
      Finset.sum_congr rfl (fun l _ => by simp only [ε]; ring)
    rw [hsum]
  have hs : schur d = fun l => ε l • t l := by
    unfold schur
    rw [← hT, KostkaModuleInversion.leftInverse]
  rw [sign_bridge, hs]
  change (-1 : ℤ) ^ evenParts lam.val.rowLens • ((-1 : ℤ) ^ evenParts lam.val.rowLens • t lam) = t lam
  rw [smul_smul, sign_mul_self, one_smul]

/-- Corollary 3.9, (3.11): `(s_λ, s_μ) = (-1)^{C(λᵀ,2)} δ_{λμ}`, assuming (3.9) in degree d. -/
theorem corollary_3_9 (d : ℕ) (h39 : Identity39 d) (lam μ : DegreeShape d) :
    quotientPairing (schur d lam : Q) (schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := by
  set σ : ℤ := (-1 : ℤ) ^ transposeChoose μ.val with hσ
  -- s_μ = σ • Σ_ρ K_{μρ} m_ρ, from (3.10).
  have hsμ : schur d μ = σ • ∑ ρ, signedKostka μ.val ρ.val • mBasis d ρ := by
    rw [← corollary_3_8 d h39 μ, smul_smul, sign_mul_self, one_smul]
  -- (h_ν, s_μ) = σ K_{μν}.
  have hpair (ν : DegreeShape d) :
      quotientPairing (hPartition ν.val) (schur d μ : Q) = σ * signedKostka μ.val ν.val := by
    rw [hsμ, Submodule.coe_smul, Submodule.coe_sum, map_zsmul, map_sum]
    simp only [Submodule.coe_smul, map_zsmul, h_m, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  -- Row vector c_λ = (s_λ, s_μ) solves Σ_λ c_λ K_{λν} = σ K_{μν}.
  have hc (ν : DegreeShape d) : ∑ l, quotientPairing (schur d l : Q) (schur d μ : Q) *
      signedKostka l.val ν.val = σ * signedKostka μ.val ν.val := by
    rw [← hpair, ← degreeHBasis_apply, schur_defining, Submodule.coe_sum, map_sum,
      LinearMap.coeFn_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [Submodule.coe_smul, map_zsmul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  have hc' (ν : DegreeShape d) : ∑ l, (if l = μ then σ else 0) * signedKostka l.val ν.val =
      σ * signedKostka μ.val ν.val := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hu := (DegreeShapes.degree_unique_solution d (fun ν => σ * signedKostka μ.val ν.val)).unique
    (y₁ := fun l => quotientPairing (schur d l : Q) (schur d μ : Q))
    (y₂ := fun l => if l = μ then σ else 0) hc hc'
  have h := congrFun hu lam
  simp only at h
  rw [h]
  split_ifs with hl
  · subst hl; rfl
  · rfl

/-! ## Unconditional in degrees d ≤ 4 (hypothesis discharged by exact computation) -/

theorem identity39_le_four (d : ℕ) (hd : d ≤ 4) : Identity39 d := by
  interval_cases d
  · exact EKSchurOrthonormalControls.identity39_0
  · exact EKSchurOrthonormalControls.identity39_1
  · exact EKSchurOrthonormalControls.identity39_2
  · exact EKSchurOrthonormalControls.identity39_3
  · exact EKSchurOrthonormalControls.identity39_4

theorem corollary_3_8_le_four (d : ℕ) (hd : d ≤ 4) (lam : DegreeShape d) :
    (-1 : ℤ) ^ transposeChoose lam.val • schur d lam =
      ∑ μ, signedKostka lam.val μ.val • mBasis d μ :=
  corollary_3_8 d (identity39_le_four d hd) lam

theorem corollary_3_9_le_four (d : ℕ) (hd : d ≤ 4) (lam μ : DegreeShape d) :
    quotientPairing (schur d lam : Q) (schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 :=
  corollary_3_9 d (identity39_le_four d hd) lam μ

/-! ## Post-production consumers: agreement with the pre-registered hand fixtures -/

theorem schur_hand1 (lam : DegreeShape 1) :
    (schur 1 lam : Q) = EKSchurOrthonormalControls.hand1 lam :=
  schur_val_unique 1 _ EKSchurOrthonormalControls.hand1_defining lam
theorem schur_hand2 (lam : DegreeShape 2) :
    (schur 2 lam : Q) = EKSchurOrthonormalControls.hand2 lam :=
  schur_val_unique 2 _ EKSchurOrthonormalControls.hand2_defining lam
theorem schur_hand3 (lam : DegreeShape 3) :
    (schur 3 lam : Q) = EKSchurOrthonormalControls.hand3 lam :=
  schur_val_unique 3 _ EKSchurOrthonormalControls.hand3_defining lam

/-- The required d = 2 fixture, now for the production s_λ: norms +1 and -1. -/
theorem degree_two_schur_norms :
    quotientPairing (schur 2 EKSchurOrthonormalControls.sh2 : Q)
        (schur 2 EKSchurOrthonormalControls.sh2 : Q) = 1 ∧
    quotientPairing (schur 2 EKSchurOrthonormalControls.sh11 : Q)
        (schur 2 EKSchurOrthonormalControls.sh11 : Q) = -1 ∧
    (schur 2 EKSchurOrthonormalControls.sh11 : Q) =
      EKElementaryQuotient.h 1 * EKElementaryQuotient.h 1 - EKElementaryQuotient.h 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [schur_hand2]; exact EKSchurOrthonormalControls.degree_two_norms.1
  · rw [schur_hand2]; exact EKSchurOrthonormalControls.degree_two_norms.2.1
  · rw [schur_hand2]; exact EKSchurOrthonormalControls.hand_values.2.2.1

end OddMath.Frontier.EKSchurOrthonormal

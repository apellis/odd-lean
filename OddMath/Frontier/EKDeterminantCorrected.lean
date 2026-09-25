import OddMath.Frontier.EKDeterminantCorrectedControls
import OddMath.Frontier.EKOddRSKII

/-!
# Corrected EK1107.5610v2 equation (3.4), all degrees

For the literal source matrix `M d ν μ = (e_ν, h_μ)` (EKDualBases.M, the
exhaustive degree-`d` partition index on both sides, integral `q = -1`
quotient pairing), we prove for EVERY `d`

  det M_d = (−1)^((p(d) − sc(d))/2) · ∏_{λ ⊢ d, λ = λᵀ} (−1)^{ℓ(w_λ)},

where `p(d)` is the number of partitions of `d`, `sc(d)` the number of
self-conjugate ones, and `ℓ(w_λ) = EKSemiorthogonality.ell λ` (strict NE/SW
cell pairs, EK p.16). The printed (3.4) is exactly the second factor
(`EKDeterminant.sourceRHS`); it is therefore correct iff `(p(d)−sc(d))/2` is
even, and fails e.g. in degree two (`EKDeterminant.equation_3_4_counterexample`).

Proof route (no degree-by-degree computation):
1. `M d ρ μ = T μ (ρᵀ)` where `T` is the Prop 2.14 triangular matrix
   `T μ ν = (h_μ, e_{νᵀ})`; i.e. `M = (Tᵀ).submatrix τ id` with `τ` conjugation.
2. `det T = ∏_{all μ} (−1)^{ℓ(μ)}` (lower triangular, unit diagonal (2.20)).
3. `det M = sign τ · det T` (`Matrix.det_permute`), and `sign τ =
   (−1)^{#2-cycles} = (−1)^((p−sc)/2)` for the involution `τ`.
4. Non-self-conjugate shapes pair off `μ ↔ μᵀ` with `ℓ(μᵀ) = ℓ(μ)`, so
   `∏_{all μ} (−1)^{ℓ(μ)} = ∏_{μ = μᵀ} (−1)^{ℓ(μ)}`.
The first invalid inference of the printed derivation is dropping `sign τ`.
Sign convention: unchanged; the sign convention remains the authority.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKDeterminantCorrected
open DegreeShapes EKDualBases EKDeterminant EKRadicalQuotient
open EKPartitionSpanning (hPartition ePartition)
local instance : DecidableEq YoungDiagram := Classical.decEq _
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- `p(d)`: the size of the exhaustive degree-`d` partition index. -/
def p (d : ℕ) : ℕ := Fintype.card (DegreeShape d)

/-- `sc(d)`: the number of self-conjugate partitions of `d`. -/
def sc (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val)).card

/-- The corrected right-hand side of (3.4). -/
def correctedRHS (d : ℕ) : ℤ := (-1 : ℤ)^((p d - sc d)/2) * sourceRHS d

/-! ### Step 1: M is a one-sided conjugation reindex of the transposed triangular matrix -/

theorem M_eq_triangular_reindex (d : ℕ) :
    M d = ((triangularMatrix d).transpose).submatrix (transposeShape d) id := by
  ext ρ μ
  rw [Matrix.submatrix_apply, Matrix.transpose_apply, triangularMatrix_apply]
  change M d ρ μ = quotientPairing (hPartition μ.val) (ePartition ρ.val.transpose.transpose)
  rw [YoungDiagram.transpose_transpose, quotientPairing_symm]
  rfl

/-! ### Step 2: the triangular determinant over ALL shapes -/

private theorem transpose_rows_injective' (d : ℕ) :
    Function.Injective (fun μ : DegreeShape d => μ.val.transpose.rowLens) := by
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.transpose_eq_iff.mp
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext h

theorem triangular_det (d : ℕ) :
    (triangularMatrix d).det = ∏ μ : DegreeShape d, (-1 : ℤ)^EKSemiorthogonality.ell μ.val := by
  letI : LinearOrder (DegreeShape d) := LinearOrder.lift'
    (fun μ : DegreeShape d => μ.val.transpose.rowLens) (transpose_rows_injective' d)
  have ht : (triangularMatrix d).BlockTriangular OrderDual.toDual := by
    intro μ ν hlt
    change μ.val.transpose.rowLens < ν.val.transpose.rowLens at hlt
    rw [triangularMatrix_apply]
    exact (EKSemiorthogonality.proposition_2_14_vanishing μ.val ν.val.transpose.rowLens
      ν.val.transpose.pos_of_mem_rowLens hlt).1
  rw [Matrix.det_of_lowerTriangular _ ht]
  exact Finset.prod_congr rfl (fun μ _ => triangularMatrix_diag d μ)

/-! ### Step 3: sign of an involution -/

/-- An involution's sign is `(−1)^(number of 2-cycles)`, i.e.
`(−1)^((#α − #fixed points)/2)`. -/
theorem sign_involution {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (h : ∀ x, σ (σ x) = x) :
    ((Equiv.Perm.sign σ : ℤˣ) : ℤ) =
      (-1 : ℤ)^((Fintype.card α - (Finset.univ.filter (fun x => σ x = x)).card)/2) := by
  have hsq : σ ^ 2 = 1 := by
    ext x
    simp [sq, h]
  have hmem : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ 2 :=
      (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hsq)
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    have h3 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsum : σ.support.card = 2 * Multiset.card σ.cycleType := by
    rw [← Equiv.Perm.sum_cycleType]
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hfix : (Finset.univ.filter (fun x => σ x = x)).card + σ.support.card =
      Fintype.card α := by
    have hs : σ.support = Finset.univ.filter (fun x => ¬ σ x = x) := by
      ext x
      simp [Equiv.Perm.mem_support]
    rw [hs, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
  have hexp : (Fintype.card α - (Finset.univ.filter (fun x => σ x = x)).card)/2 =
      Multiset.card σ.cycleType := by
    omega
  rw [hexp, Equiv.Perm.sign_of_cycleType]
  conv_lhs => rw [hrep]
  rw [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  push_cast
  rw [pow_add, pow_mul', neg_one_sq, one_pow, one_mul]

theorem transposeShape_involutive (d : ℕ) (μ : DegreeShape d) :
    transposeShape d (transposeShape d μ) = μ := by
  apply Subtype.ext
  change μ.val.transpose.transpose = μ.val
  exact YoungDiagram.transpose_transpose _

theorem transposeShape_fixed_card (d : ℕ) :
    (Finset.univ.filter (fun μ : DegreeShape d => transposeShape d μ = μ)).card = sc d := by
  unfold sc
  congr 1
  ext μ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Subtype.ext_iff

/-- `sign τ = (−1)^((p(d) − sc(d))/2)` for conjugation `τ` on degree-`d` shapes. -/
theorem sign_transposeShape (d : ℕ) :
    ((Equiv.Perm.sign (transposeShape d) : ℤˣ) : ℤ) = (-1 : ℤ)^((p d - sc d)/2) := by
  rw [sign_involution _ (transposeShape_involutive d), transposeShape_fixed_card]
  rfl

/-- `p(d) − sc(d)` is even: it is twice the number of 2-cycles. -/
theorem p_sub_sc_even (d : ℕ) : Even (p d - sc d) := by
  -- The non-self-conjugate shapes are the support of τ; its cardinality is the cycle-type sum.
  have hsupp : (Equiv.Perm.support (transposeShape d)).card + sc d = p d := by
    rw [← transposeShape_fixed_card, add_comm]
    have hs' : (Equiv.Perm.support (transposeShape d)) =
        Finset.univ.filter (fun μ => ¬ transposeShape d μ = μ) := by
      ext μ
      simp [Equiv.Perm.mem_support]
    rw [hs', Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
    rfl
  have hev : Even (Equiv.Perm.support (transposeShape d)).card := by
    have hmem : ∀ n ∈ Equiv.Perm.cycleType (transposeShape d), n = 2 := by
      intro n hn
      have h1 : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans
        (orderOf_dvd_of_pow_eq_one (by ext μ; simp [sq, transposeShape_involutive]))
      have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
      have h3 := Nat.le_of_dvd (by norm_num) h1
      omega
    rw [← Equiv.Perm.sum_cycleType, Multiset.eq_replicate.mpr ⟨rfl, hmem⟩,
      Multiset.sum_replicate, smul_eq_mul]
    exact even_two.mul_left _
  have : p d - sc d = (Equiv.Perm.support (transposeShape d)).card := by omega
  rw [this]
  exact hev

/-! ### Step 4: non-self-conjugate shapes cancel in pairs -/

theorem prod_all_eq_sourceRHS (d : ℕ) :
    ∏ μ : DegreeShape d, (-1 : ℤ)^EKSemiorthogonality.ell μ.val = sourceRHS d := by
  have hnot : ∏ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => ¬ μ.val.transpose = μ.val),
      (-1 : ℤ)^EKSemiorthogonality.ell μ.val = 1 := by
    apply Finset.prod_involution (fun μ _ => transposeShape d μ)
    · intro μ _
      change (-1 : ℤ)^EKSemiorthogonality.ell μ.val *
        (-1 : ℤ)^EKSemiorthogonality.ell μ.val.transpose = 1
      rw [EKOddRSKII.ell_transpose, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    · intro μ hμ _ heq
      exact (Finset.mem_filter.mp hμ).2 (congrArg Subtype.val heq)
    · intro μ hμ
      rw [Finset.mem_filter] at hμ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      change ¬ μ.val.transpose.transpose = μ.val.transpose
      rw [YoungDiagram.transpose_transpose]
      exact fun h => hμ.2 h.symm
    · intro μ _
      exact transposeShape_involutive d μ
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun μ : DegreeShape d => μ.val.transpose = μ.val), hnot, mul_one]
  rfl

/-! ### Main theorem -/

/-- `det M_d = sign τ · ∏_{ALL μ ⊢ d} (−1)^{ℓ(μ)}` (intermediate closed form). -/
theorem det_M_sign_prod (d : ℕ) :
    (M d).det = ((Equiv.Perm.sign (transposeShape d) : ℤˣ) : ℤ) *
      ∏ μ : DegreeShape d, (-1 : ℤ)^EKSemiorthogonality.ell μ.val := by
  rw [M_eq_triangular_reindex, Matrix.det_permute, Matrix.det_transpose, triangular_det,
    Int.cast_id]

/-- **Corrected (3.4), every degree `d`, literal `M d`, exhaustive index.** -/
theorem corrected_equation_3_4 (d : ℕ) : (M d).det = correctedRHS d := by
  rw [det_M_sign_prod, sign_transposeShape, prod_all_eq_sourceRHS]
  rfl

/-- Explicit form, in partition statistics only. -/
theorem corrected_equation_3_4_explicit (d : ℕ) :
    (M d).det = (-1 : ℤ)^((Fintype.card (DegreeShape d) -
        (Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val)).card)/2) *
      ∏ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => μ.val.transpose = μ.val),
        (-1 : ℤ)^EKSemiorthogonality.ell μ.val :=
  corrected_equation_3_4 d

/-- Corollary: corrected = printed · (−1)^((p−sc)/2). -/
theorem corrected_eq_source_mul (d : ℕ) :
    correctedRHS d = sourceRHS d * (-1 : ℤ)^((p d - sc d)/2) := mul_comm _ _

/-- The printed RHS is a unit sign. -/
theorem sourceRHS_sq (d : ℕ) : sourceRHS d * sourceRHS d = 1 := by
  unfold sourceRHS
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro μ _
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- Exactly when the printed (3.4) holds: iff `(p(d) − sc(d))/2` is even. -/
theorem printed_iff (d : ℕ) : (M d).det = sourceRHS d ↔ Even ((p d - sc d)/2) := by
  rw [corrected_equation_3_4, correctedRHS]
  have hne : sourceRHS d ≠ 0 := by
    intro h0
    have := sourceRHS_sq d
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  constructor
  · intro h
    have h1 : (-1 : ℤ)^((p d - sc d)/2) = 1 := by
      have := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
      exact this
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h1
  · intro h
    rw [Even.neg_one_pow h, one_mul]

/-- Consumer consistency with the kernel-checked degree-two refutation. -/
theorem degree_two : correctedRHS 2 = -1 ∧ (M 2).det = correctedRHS 2 ∧
    (M 2).det ≠ sourceRHS 2 :=
  ⟨(corrected_equation_3_4 2).symm.trans degree_two_det, corrected_equation_3_4 2,
    equation_3_4_counterexample⟩

/-- Degree-two statistics computed from the definitions (not from det M₂). -/
theorem degree_two_stats : p 2 = 2 ∧ sc 2 = 0 :=
  ⟨EKDeterminantCorrectedControls.degree_two_card, EKDeterminantCorrectedControls.degree_two_sc⟩

theorem degree_two_direct : correctedRHS 2 = -1 := by
  rw [correctedRHS, degree_two_stats.1, degree_two_stats.2, degree_two_rhs]
  norm_num

/-! ### Frozen statement shape -/

/-- `F d`: the corrected closed right-hand side, in partition statistics only
(`p d`, `sc d`, and `ell` of self-conjugate shapes). -/
def F (d : ℕ) : ℤ := (-1 : ℤ)^((p d - sc d)/2) * sourceRHS d

/-- **Frozen target**: `det M_d = F d` for every `d`. -/
theorem det_M (d : ℕ) : (M d).det = F d := corrected_equation_3_4 d

theorem F_two : F 2 = -1 := degree_two_direct

theorem F_two_agrees : F 2 = (M 2).det := F_two.trans degree_two_det.symm

/-- Relation to the print: `F d = sourceRHS d · (−1)^((p(d) − sc(d))/2)`. -/
theorem F_eq_source_mul (d : ℕ) : F d = sourceRHS d * (-1 : ℤ)^((p d - sc d)/2) :=
  mul_comm _ _

end OddMath.Frontier.EKDeterminantCorrected

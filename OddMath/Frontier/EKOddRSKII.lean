import OddMath.Frontier.EKOddRSKIIControls
import OddMath.Frontier.EKAutomorphisms

/-!
# EK1107.5610v2 p.30: Corollary 3.12 (3.14) and Corollary 3.13 "Odd RSK II" (3.15)

Source (printed p.30, frozen source excerpt PAGE 30):

  Corollary 3.12.  (-1)^{(μ 2)+|μ|} e_μ = Σ_{λ⊢n} (-1)^{ℓ(w_λ)+|λ|} K_{λᵀμ} s_λ,
                   (-1)^{ℓ(w_λ)+(λᵀ 2)+|λ|} s_λ = Σ_{μ⊢n} (-1)^{(μ 2)+|μ|} K_{λᵀμ} f_μ.   (3.14)
  Proof. Apply ψ1ψ2 to equations (3.6) and (3.10).
  Corollary 3.13.  (-1)^{(μ 2)+|μ|+(ρ 2)+|ρ|} M″_{μρ} = Σ_λ (-1)^{(λᵀ 2)} K_{λᵀμ}K_{λᵀρ}
                   = Σ_λ (-1)^{λ₂+λ₄+λ₆+…} K_{λᵀμ}K_{λᵀρ}.                           (3.15)

Objects (all existing or defined here, no surrogate):
* `schur d λ` = s_λ: the unique solution of (3.6) `h_μ = Σ_λ K_{λμ} s_λ` in the actual degree-d
  piece of Q, i.e. `KostkaModuleInversion.recover d (degreeHBasis d)` (literally the same term as `EKSchurOrthonormal.schur`).
* K = `TableauDominance.signedKostka`; e_μ = `degreeEBasis`; f_μ = `EKDualBases.fBasis`;
  M″ = `EKDualBases.Me` = (e,e); ψ1ψ2 = `EKAutomorphisms.psi12` (ψ1 after ψ2).
* ℓ(w_λ) = `EKSemiorthogonality.ell` (the NE-pair count; the fixed convention's
  `triangularMatrix_diag` sign is (-1)^{ell}).  (α 2) = Σ C(α_i,2).

What is proved:
* UNCONDITIONAL, every degree d:
  `first312_iff_lemma311` : (3.14, first) in degree d  ⟺  EK (3.13) in degree d;
  `second312_iff_dualRSK` : (3.14, second) in degree d ⟺ the integer identity `DualRSK d`;
  `sign_bridge`, `ell_transpose`, `psi12_hPartition`.
* UNCONDITIONAL for d ≤ 4 (via the pre-registered controls): (3.14) both, (3.15) both, and
  consequently (3.13) and `DualRSK`.
* CONDITIONAL (labelled), every degree d, on EXACTLY the printed hypotheses
  (3.13) [`Lemma311 d`] and (3.11) [`Cor39 d`]:
  `CONDITIONAL_cor_3_12_first`, `CONDITIONAL_cor_3_12_second`, `CONDITIONAL_cor_3_13`.
No Lemma 2.15 / Prop 3.10 route, no general RSK, no reproof of (3.9)–(3.11) or (3.13).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKOddRSKII
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition ePartition)
open EKOddRSKIIControls (evenParts transposeChoose rowChoose Esrc sigmaSrc Xsrc sC pair_ee
  pair_e_sC ext_e second_of_dual)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Sign statistics -/

/-- Reproduced verbatim from `EKSchurOrthonormal`. -/
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

/-- `(-1)^{(λᵀ 2)} = (-1)^{λ₂+λ₄+λ₆+…}` for every diagram (second equality of (3.15)). -/
theorem sign_bridge (μ : YoungDiagram) :
    (-1 : ℤ) ^ transposeChoose μ = (-1 : ℤ) ^ evenParts μ.rowLens := by
  rw [transposeChoose_eq, ← cells_fst_sum_cols, cells_fst_sum_rows, parity, evenParts_rowLens]

/-- ℓ(w_{λᵀ}) = ℓ(w_λ): transposition swaps the two cells of each strict NE/SW pair. -/
theorem ell_transpose (μ : YoungDiagram) :
    EKSemiorthogonality.ell μ.transpose = EKSemiorthogonality.ell μ := by
  unfold EKSemiorthogonality.ell
  simp only [Finset.card_filter]
  have hc : μ.transpose.cells = μ.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding := by
    change (Equiv.prodComm ℕ ℕ).finsetCongr μ.cells = _
    rw [Equiv.finsetCongr_apply]
  rw [hc, Finset.sum_map]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Equiv.prodComm_apply, Prod.fst_swap,
    Prod.snd_swap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> first | rfl | (exfalso; omega)

theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp [YoungDiagram.card, YoungDiagram.transpose]

theorem transposeShape_invol (d : ℕ) (lam : DegreeShape d) :
    transposeShape d (transposeShape d lam) = lam := by
  apply Subtype.ext
  change lam.val.transpose.transpose = lam.val
  exact YoungDiagram.transpose_transpose _

/-! ## ψ1ψ2 on the complete and elementary partition products -/

theorem wordSign_eq (w : List ℕ) :
    EKAutomorphisms.wordSign w = (-1 : ℤ) ^ ((w.map (fun a => a.choose 2)).sum + w.sum) := by
  induction w with
  | nil => simp [EKAutomorphisms.wordSign]
  | cons a w ih =>
    simp only [EKAutomorphisms.wordSign, List.map_cons, List.prod_cons, List.sum_cons] at ih ⊢
    rw [ih, EKAutomorphisms.s, Nat.choose_succ_succ, Nat.choose_one_right, ← pow_add]
    congr 1
    ring

theorem wordSign_hPartition (μ : YoungDiagram) :
    EKAutomorphisms.wordSign μ.rowLens = (-1 : ℤ) ^ (rowChoose μ + μ.card) := by
  rw [wordSign_eq, rowLens_sum]
  rfl

/-- ψ1ψ2(h_μ) = (-1)^{(μ 2)+|μ|} e_μ. -/
theorem psi12_hPartition (μ : YoungDiagram) :
    EKAutomorphisms.psi12 (hPartition μ) = ((-1 : ℤ) ^ (rowChoose μ + μ.card)) • ePartition μ := by
  have h := EKAutomorphisms.psi12_hWord μ.rowLens
  rw [wordSign_hPartition] at h
  exact h

/-- ψ1ψ2(e_μ) = (-1)^{(μ 2)+|μ|} h_μ. -/
theorem psi12_ePartition (μ : YoungDiagram) :
    EKAutomorphisms.psi12 (ePartition μ) = ((-1 : ℤ) ^ (rowChoose μ + μ.card)) • hPartition μ := by
  have h := EKAutomorphisms.psi12_eWord μ.rowLens
  rw [wordSign_hPartition] at h
  exact h

/-! ## The source s_λ, inside the actual degree-d piece -/

/-- s_λ := unique solution of (3.6) (identical term to `EKSchurOrthonormal.schur`). -/
def schur (d : ℕ) : DegreeShape d → degreePiece d :=
  KostkaModuleInversion.recover d (degreeHBasis d)

theorem schur_eq_sC (d : ℕ) : schur d = sC d := rfl

/-- (3.6), literally, in Q. -/
theorem schur_defining (d : ℕ) (μ : DegreeShape d) :
    hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • (schur d lam : Q) := by
  have h := congrArg Subtype.val (congrFun (KostkaModuleInversion.rightInverse d (degreeHBasis d)) μ)
  rw [← degreeHBasis_apply, ← h]
  change ((∑ lam, signedKostka lam.val μ.val • schur d lam : degreePiece d) : Q) = _
  simp only [Submodule.coe_sum, Submodule.coe_smul]

/-- (3.6) determines s uniquely when tested in Q. -/
theorem schur_val_unique (d : ℕ) (S : DegreeShape d → Q)
    (hS : ∀ μ : DegreeShape d, hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • S lam) :
    ∀ lam, S lam = (schur d lam : Q) := by
  have h1 : KostkaModuleInversion.transform d S = fun μ => hPartition μ.val := by
    funext μ; exact (hS μ).symm
  have h2 : KostkaModuleInversion.transform d (fun lam => (schur d lam : Q)) =
      fun μ => hPartition μ.val := by
    funext μ; exact (schur_defining d μ).symm
  intro lam
  have hu := KostkaModuleInversion.uniqueSolution d (fun μ : DegreeShape d => hPartition μ.val)
  exact congrFun (hu.unique h1 h2) lam

/-! ## Exact printed statements, degreewise -/

/-- EK Lemma 3.11 (3.13) in degree d, as printed: ψ1ψ2(s_λ) = (-1)^{ℓ(w_λ)+|λ|} s_{λᵀ}. -/
def Lemma311 (d : ℕ) : Prop := ∀ lam : DegreeShape d,
  EKAutomorphisms.psi12 (schur d lam : Q) =
    ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card)) • (schur d (transposeShape d lam) : Q)

/-- EK Corollary 3.9 (3.11) in degree d, as printed (same form as `EKSchurOrthonormal.corollary_3_9`). -/
def Cor39 (d : ℕ) : Prop := ∀ lam μ : DegreeShape d,
  quotientPairing (schur d lam : Q) (schur d μ : Q) =
    if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0

/-- (3.14), first equation, in degree d, as printed. -/
def First312 (d : ℕ) : Prop := ∀ μ : DegreeShape d,
  ((-1 : ℤ) ^ (rowChoose μ.val + μ.val.card)) • degreeEBasis d μ =
    ∑ lam, ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card) *
      signedKostka lam.val.transpose μ.val) • schur d lam

/-- (3.14), second equation, in degree d, as printed. -/
def Second312 (d : ℕ) : Prop := ∀ lam : DegreeShape d,
  ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val + lam.val.card)) • schur d lam =
    ∑ μ, ((-1 : ℤ) ^ (rowChoose μ.val + μ.val.card) * signedKostka lam.val.transpose μ.val) •
      fBasis d μ

/-- (3.15), both printed equalities, on the literal (e,e) Gram entries `EKDualBases.Me`. -/
def OddRSKII (d : ℕ) : Prop := ∀ μ ρ : DegreeShape d,
  (-1 : ℤ) ^ (rowChoose μ.val + μ.val.card + (rowChoose ρ.val + ρ.val.card)) * Me d μ ρ =
    ∑ lam : DegreeShape d, (-1 : ℤ) ^ transposeChoose lam.val *
      signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val ∧
  ∑ lam : DegreeShape d, (-1 : ℤ) ^ transposeChoose lam.val *
      signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val =
    ∑ lam : DegreeShape d, (-1 : ℤ) ^ evenParts lam.val.rowLens *
      signedKostka lam.val.transpose μ.val * signedKostka lam.val.transpose ρ.val

/-- Integer "dual" identity: M_{νj} = Σ_λ (-1)^{ℓ(w_λ)+(λᵀ 2)+d} (-1)^{(ν 2)+d} K_{λᵀν} K_{λj},
with M = (e,h) (`EKDualBases.M`).  Not a hypothesis anywhere: only an equivalent form. -/
def DualRSK (d : ℕ) : Prop := ∀ ν j : DegreeShape d,
  ∑ lam, Xsrc d ν lam * signedKostka lam.val j.val = M d ν j

/-! ## (3.14, first) ⟺ (3.13), every degree (unconditional) -/

theorem first312_of_lemma311 (d : ℕ) (h : Lemma311 d) : First312 d := by
  intro μ
  apply Subtype.ext
  have hμ := congrArg EKAutomorphisms.psi12 (schur_defining d μ)
  rw [psi12_hPartition, map_sum] at hμ
  simp only [map_zsmul] at hμ
  simp only [Submodule.coe_sum, Submodule.coe_smul, degreeEBasis_apply]
  rw [hμ, ← Equiv.sum_comp (transposeShape d)]
  apply Finset.sum_congr rfl
  intro lam _
  rw [h (transposeShape d lam), transposeShape_invol, smul_smul]
  congr 1
  change signedKostka lam.val.transpose μ.val *
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val.transpose + lam.val.transpose.card) = _
  rw [ell_transpose, card_transpose, mul_comm]

theorem lemma311_of_first312 (d : ℕ) (h : First312 d) : Lemma311 d := by
  -- T_κ := (-1)^{ℓ(w_κ)+|κ|} ψ1ψ2(s_{κᵀ}) solves (3.6), hence equals s_κ.
  have hT := schur_val_unique d (fun κ => ((-1 : ℤ) ^ (EKSemiorthogonality.ell κ.val + κ.val.card)) •
    EKAutomorphisms.psi12 (schur d (transposeShape d κ) : Q)) (by
      intro μ
      have hμ := congrArg (fun x : degreePiece d => EKAutomorphisms.psi12 (x : Q)) (h μ)
      simp only [Submodule.coe_smul, Submodule.coe_sum, degreeEBasis_apply, map_zsmul, map_sum,
        psi12_ePartition, smul_smul, EKOddRSKIIControls.neg_one_sq, one_smul] at hμ
      rw [hμ, ← Equiv.sum_comp (transposeShape d)]
      apply Finset.sum_congr rfl
      intro κ _
      beta_reduce
      rw [smul_smul]
      congr 1
      change (-1 : ℤ) ^ (EKSemiorthogonality.ell κ.val.transpose + κ.val.transpose.card) *
          signedKostka κ.val.transpose.transpose μ.val = _
      rw [ell_transpose, card_transpose, YoungDiagram.transpose_transpose, mul_comm])
  intro lam
  have h1 := hT (transposeShape d lam)
  simp only [transposeShape_invol] at h1
  have h2 := congrArg (fun x : Q => ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card)) • x) h1
  simp only [smul_smul] at h2
  change ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card) *
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val.transpose + lam.val.transpose.card)) •
      EKAutomorphisms.psi12 (schur d lam : Q) = _ at h2
  rw [ell_transpose, card_transpose, EKOddRSKIIControls.neg_one_sq, one_smul] at h2
  exact h2

/-- UNCONDITIONAL: the first equation of (3.14) in degree d is EQUIVALENT to (3.13) in degree d. -/
theorem first312_iff_lemma311 (d : ℕ) : First312 d ↔ Lemma311 d :=
  ⟨lemma311_of_first312 d, first312_of_lemma311 d⟩

/-! ## (3.14, second) ⟺ DualRSK, every degree (unconditional) -/

theorem second312_of_dualRSK (d : ℕ) (h : DualRSK d) : Second312 d := by
  intro lam
  exact second_of_dual d h lam

theorem pair_e_schur_of_second (d : ℕ) (h : Second312 d) (ν lam : DegreeShape d) :
    quotientPairing (ePartition ν.val) (schur d lam : Q) = Xsrc d ν lam := by
  have h1 := congrArg (fun x : degreePiece d => quotientPairing (ePartition ν.val) (x : Q)) (h lam)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, smul_eq_mul, e_f,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have h2 := congrArg (fun z : ℤ =>
    (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val + lam.val.card) * z) h1
  simp only [← mul_assoc, EKOddRSKIIControls.neg_one_sq, one_mul] at h2
  rw [h2]
  unfold Xsrc sigmaSrc Esrc
  rw [lam.property, ν.property]

theorem dualRSK_of_second312 (d : ℕ) (h : Second312 d) : DualRSK d := by
  intro ν j
  have hj := congrArg (fun x : Q => quotientPairing (ePartition ν.val) x) (schur_defining d j)
  simp only [map_sum, map_zsmul, smul_eq_mul, pair_e_schur_of_second d h] at hj
  change _ = quotientPairing (ePartition ν.val) (hPartition j.val)
  rw [hj]
  apply Finset.sum_congr rfl
  intro lam _
  ring

/-- UNCONDITIONAL: the second equation of (3.14) in degree d is EQUIVALENT to `DualRSK d`. -/
theorem second312_iff_dualRSK (d : ℕ) : Second312 d ↔ DualRSK d :=
  ⟨dualRSK_of_second312 d, second312_of_dualRSK d⟩

/-! ## From (3.14, first) and (3.11): the e-pairings of s, (3.14, second) and (3.15) -/

theorem pair_e_schur_of_first_cor39 (d : ℕ) (h1 : First312 d) (h311 : Cor39 d)
    (ν κ : DegreeShape d) :
    quotientPairing (ePartition ν.val) (schur d κ : Q) = Xsrc d ν κ := by
  simp only [Cor39] at h311
  have hν := congrArg (fun x : degreePiece d => quotientPairing (x : Q) (schur d κ : Q)) (h1 ν)
  simp only [Submodule.coe_sum, Submodule.coe_smul, degreeEBasis_apply, map_sum, map_zsmul,
    LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, smul_eq_mul, h311,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hν
  have h2 := congrArg (fun z : ℤ => (-1 : ℤ) ^ (rowChoose ν.val + ν.val.card) * z) hν
  simp only [← mul_assoc, EKOddRSKIIControls.neg_one_sq, one_mul] at h2
  rw [h2]
  unfold Xsrc sigmaSrc Esrc
  rw [κ.property, ν.property]
  ring

theorem dualRSK_of_first_cor39 (d : ℕ) (h1 : First312 d) (h311 : Cor39 d) : DualRSK d := by
  intro ν j
  have hj := congrArg (fun x : Q => quotientPairing (ePartition ν.val) x) (schur_defining d j)
  simp only [map_sum, map_zsmul, smul_eq_mul, pair_e_schur_of_first_cor39 d h1 h311] at hj
  change _ = quotientPairing (ePartition ν.val) (hPartition j.val)
  rw [hj]
  apply Finset.sum_congr rfl
  intro lam _
  ring

theorem oddRSKII_of_first_cor39 (d : ℕ) (h1 : First312 d) (h311 : Cor39 d) : OddRSKII d := by
  intro μ ρ
  refine ⟨?_, ?_⟩
  · have hρ := congrArg (fun x : degreePiece d => quotientPairing (ePartition μ.val) (x : Q)) (h1 ρ)
    simp only [Submodule.coe_sum, Submodule.coe_smul, degreeEBasis_apply, map_sum, map_zsmul,
      smul_eq_mul, pair_ee, pair_e_schur_of_first_cor39 d h1 h311] at hρ
    have h2 := congrArg (fun z : ℤ => (-1 : ℤ) ^ (rowChoose μ.val + μ.val.card) * z) hρ
    simp only at h2
    rw [pow_add, mul_assoc, h2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lam _
    unfold Xsrc sigmaSrc Esrc
    rw [lam.property, μ.property]
    have eL := EKOddRSKIIControls.neg_one_sq (EKSemiorthogonality.ell lam.val)
    have eD := EKOddRSKIIControls.neg_one_sq d
    have eA := EKOddRSKIIControls.neg_one_sq (rowChoose μ.val)
    set L : ℤ := (-1) ^ EKSemiorthogonality.ell lam.val
    set D : ℤ := (-1) ^ d
    set A : ℤ := (-1) ^ rowChoose μ.val
    linear_combination ((-1 : ℤ) ^ transposeChoose lam.val * signedKostka lam.val.transpose μ.val *
        signedKostka lam.val.transpose ρ.val) * (D ^ 4 * L ^ 2 * eA + (D ^ 2 + 1) * L ^ 2 * eD + eL)
  · apply Finset.sum_congr rfl
    intro lam _
    rw [sign_bridge]

/-! ## Under (3.11): (3.14, second) ⟹ (3.14, first); the missing inference is ONE statement -/

/-- The s_λ span the degree piece (from (3.6) and the complete basis). -/
theorem schur_span (d : ℕ) (x : degreePiece d) :
    ∃ a : DegreeShape d → ℤ, (x : Q) = ∑ lam, a lam • (schur d lam : Q) := by
  refine ⟨fun lam => ∑ j, (degreeHBasis d).repr x j * signedKostka lam.val j.val, ?_⟩
  have hx := congrArg Subtype.val ((degreeHBasis d).sum_repr x)
  rw [← hx]
  simp only [Submodule.coe_sum, Submodule.coe_smul, degreeHBasis_apply, schur_defining,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem first312_of_second312_cor39 (d : ℕ) (h2 : Second312 d) (h311 : Cor39 d) : First312 d := by
  have h311' := h311
  simp only [Cor39] at h311'
  intro μ
  obtain ⟨a, ha⟩ := schur_span d (degreeEBasis d μ)
  have hcoef : ∀ κ, a κ = (-1 : ℤ) ^ transposeChoose κ.val * Xsrc d μ κ := by
    intro κ
    have hp := congrArg (fun x : Q => quotientPairing x (schur d κ : Q)) ha
    simp only [degreeEBasis_apply, pair_e_schur_of_second d h2, map_sum, map_zsmul,
      LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, smul_eq_mul, h311',
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hp
    rw [hp, mul_comm, mul_assoc, EKOddRSKIIControls.neg_one_sq, mul_one]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [degreeEBasis_apply] at ha
  rw [degreeEBasis_apply, ha, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro κ _
  rw [smul_smul, hcoef κ]
  congr 1
  unfold Xsrc sigmaSrc Esrc
  rw [κ.property, μ.property]
  have eA := EKOddRSKIIControls.neg_one_sq (rowChoose μ.val)
  have eC := EKOddRSKIIControls.neg_one_sq (transposeChoose κ.val)
  have eD := EKOddRSKIIControls.neg_one_sq d
  set A : ℤ := (-1) ^ rowChoose μ.val
  set C : ℤ := (-1) ^ transposeChoose κ.val
  set Dd : ℤ := (-1) ^ d
  linear_combination ((-1 : ℤ) ^ EKSemiorthogonality.ell κ.val * Dd *
      signedKostka κ.val.transpose μ.val) * (C ^ 2 * Dd ^ 2 * eA + Dd ^ 2 * eC + eD)

/-- UNCONDITIONAL reduction: granted (3.11), (3.13), both equations of (3.14) and `DualRSK`
are pairwise EQUIVALENT in each degree, and each implies (3.15). -/
theorem equivalences_of_cor39 (d : ℕ) (h311 : Cor39 d) :
    (Lemma311 d ↔ First312 d) ∧ (First312 d ↔ Second312 d) ∧ (Second312 d ↔ DualRSK d) ∧
      (First312 d → OddRSKII d) :=
  ⟨(first312_iff_lemma311 d).symm,
   ⟨fun h1 => second312_of_dualRSK d (dualRSK_of_first_cor39 d h1 h311),
    fun h2 => first312_of_second312_cor39 d h2 h311⟩,
   second312_iff_dualRSK d,
   fun h1 => oddRSKII_of_first_cor39 d h1 h311⟩

/-! ## CONDITIONAL theorems (labelled): hypotheses are EXACTLY (3.13) and (3.11) -/

/-- CONDITIONAL on EK (3.13) in degree d: (3.14), first equation. -/
theorem CONDITIONAL_cor_3_12_first (d : ℕ) (h313 : Lemma311 d) : First312 d :=
  first312_of_lemma311 d h313

/-- CONDITIONAL on EK (3.13) and (3.11) in degree d: (3.14), second equation. -/
theorem CONDITIONAL_cor_3_12_second (d : ℕ) (h313 : Lemma311 d) (h311 : Cor39 d) : Second312 d :=
  second312_of_dualRSK d (dualRSK_of_first_cor39 d (first312_of_lemma311 d h313) h311)

/-- CONDITIONAL on EK (3.13) and (3.11) in degree d: (3.15), both equalities. -/
theorem CONDITIONAL_cor_3_13 (d : ℕ) (h313 : Lemma311 d) (h311 : Cor39 d) : OddRSKII d :=
  oddRSKII_of_first_cor39 d (first312_of_lemma311 d h313) h311

/-! ## UNCONDITIONAL for every d ≤ 4 (pre-registered exact controls) -/

theorem first312_le_four (d : ℕ) (hd : d ≤ 4) : First312 d :=
  fun μ => EKOddRSKIIControls.cor_3_12_first_le_four d hd μ

theorem second312_le_four (d : ℕ) (hd : d ≤ 4) : Second312 d :=
  fun lam => EKOddRSKIIControls.cor_3_12_second_le_four d hd lam

theorem dualRSK_le_four (d : ℕ) (hd : d ≤ 4) : DualRSK d :=
  EKOddRSKIIControls.dual_le_four d hd

theorem oddRSKII_le_four (d : ℕ) (hd : d ≤ 4) : OddRSKII d := by
  intro μ ρ
  rw [μ.property, ρ.property]
  exact EKOddRSKIIControls.cor_3_13_le_four d hd μ ρ

/-- Consequence of the controls and the unconditional equivalence (not a reproof of Lemma 3.11
in general): (3.13) holds in every degree d ≤ 4. -/
theorem lemma311_le_four (d : ℕ) (hd : d ≤ 4) : Lemma311 d :=
  lemma311_of_first312 d (first312_le_four d hd)

end OddMath.Frontier.EKOddRSKII

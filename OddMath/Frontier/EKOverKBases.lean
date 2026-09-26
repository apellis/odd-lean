import OddMath.Frontier.EKOverKStructure
import OddMath.Frontier.EKFinalClosure
import OddMath.Frontier.EKClosureComposition

/-!
# EK Lemma 2.16, §3.1, Cor. 3.9 and Lemma 3.11 over an arbitrary commutative ring

Source: Ellis–Khovanov, arXiv:1107.5610v2.  `k` is an arbitrary commutative ring, `q = -1`,
`Λ_k = Lam (-1 : k)`; all statements are base changes of the integral ones.

* Lemma 2.16 (p. 18) over `k` (`lemma_2_16_K`): the matrix of ψ₃ in the basis `{h_λ}` is
  triangular for the lexicographic order, with diagonal entries `(-1)^{b(λᵀ)}`.
* §3.1 (p. 23) over `k`: the odd forgotten functions `f_λ` form a `k`-basis of `Λ_k`
  (`fBasisK`) dual to `{e_λ}` for the form (2.1) (`form_eBasisK_fK`).
* §3.3 (pp. 26–28) over `k`: the odd Schur functions `s_λ` form a `k`-basis of `Λ_k`
  (`sBasisK`), orthogonal with `(s_λ, s_λ) = (-1)^{C(λᵀ,2)}` (Cor. 3.9, (3.11),
  `corollary_3_9_K`), and related to the `h_μ` by (3.6) (`hBasisK_eq_sum_sK`).
* Lemma 3.11 (p. 28), (3.13), over `k` (`lemma_3_11_K`):
  `ψ₁ψ₂(s_λ) = (-1)^{ℓ(w_λ)+|λ|} s_{λᵀ}`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ DegreeShapes

variable {k : Type*} [CommRing k]

local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
attribute [local instance] Classical.propDecidable

/-! ## Coordinates in the `h`-basis -/

theorem hBasisK_eq_psiRing (μ : YoungDiagram) :
    hBasisK (k := k) μ = psiRing (EKPartitionSpanning.hPartition μ) := by
  rw [hBasisK_apply, psi_hPartition]

/-- The `h`-coordinates of an image of `Λ_ℤ` are the images of the integral coordinates. -/
theorem hBasisK_repr_psiRing (z : QZ) (ν : YoungDiagram) :
    (hBasisK (k := k)).repr (psiRing z) ν = ((EKIntegralBases.hBasis.repr z ν : ℤ) : k) := by
  rw [hBasisK, Basis.map_repr, LinearEquiv.trans_apply, baseChangeEquiv_symm_psiRing,
    Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_one]

/-- **EK Lemma 2.16 over every commutative ring `k`.**  In the basis `{h_λ}` of `Λ_k`,
`ψ₃(h_λ) = (-1)^{b(λᵀ)} h_λ + (a combination of h_ν with |ν| = |λ| and ν >_lex λ)`. -/
theorem lemma_2_16_K (μ : YoungDiagram) :
    (hBasisK (k := k)).repr (psi3K k (hBasisK μ)) μ = (-1 : k) ^ (EKTriangular.b μ.transpose) ∧
    ∀ ν : YoungDiagram, (ν.card ≠ μ.card ∨ ¬ (ν = μ ∨ List.Lex (· < ·) μ.rowLens ν.rowLens)) →
      (hBasisK (k := k)).repr (psi3K k (hBasisK μ)) ν = 0 := by
  refine ⟨?_, fun ν hν => ?_⟩
  · rw [hBasisK_eq_psiRing, psi3K_psiRing, hBasisK_repr_psiRing]
    rw [EKTriangular.psi3_diagonal]
    push_cast; rfl
  · rw [hBasisK_eq_psiRing, psi3K_psiRing, hBasisK_repr_psiRing]
    rw [EKTriangular.psi3_coordinate_zero μ ν hν, Int.cast_zero]

/-! ## Pairings of images -/

theorem form_psiRing (a b : QZ) :
    quotientForm (-1 : k) (psiRing a) (psiRing b) =
      ((EKRadicalQuotient.quotientPairing a b : ℤ) : k) :=
  EKFinal.quotientForm_psiRing a b

theorem mem_degreePiece_card (μ : YoungDiagram) :
    EKPartitionSpanning.ePartition μ ∈ EKIntegralBases.degreePiece μ.card := by
  rw [EKIntegralBases.degreePiece_eq_ePartition_span]
  exact Submodule.subset_span ⟨⟨μ, rfl⟩, rfl⟩

theorem hPartition_mem_card (μ : YoungDiagram) :
    EKPartitionSpanning.hPartition μ ∈ EKIntegralBases.degreePiece μ.card := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span]
  exact Submodule.subset_span ⟨⟨μ, rfl⟩, rfl⟩

/-! ## The forgotten basis `{f_λ}` over `k` -/

variable (k) in
/-- `f_λ ∈ Λ_k`, the image of the integral odd forgotten function (EK §3.1). -/
def fK (μ : YoungDiagram) : LamK k :=
  psiRing ((EKDualBases.fBasis μ.card ⟨μ, rfl⟩ : EKIntegralBases.degreePiece μ.card) : QZ)

theorem fK_shape {d : ℕ} (μ : DegreeShape d) :
    fK k μ.val = psiRing ((EKDualBases.fBasis d μ : EKIntegralBases.degreePiece d) : QZ) := by
  obtain ⟨μ, rfl⟩ := μ
  rfl

/-- **EK §3.1 over `k`:** `(e_ν, f_μ) = δ_{νμ}`. -/
theorem form_eBasisK_fK (ν μ : YoungDiagram) :
    quotientForm (-1 : k) (eBasisK ν) (fK k μ) = if ν = μ then 1 else 0 := by
  rw [eBasisK_eq_psi, fK, form_psiRing]
  by_cases hd : ν.card = μ.card
  · have h := EKDualBases.e_f μ.card ⟨ν, hd⟩ ⟨μ, rfl⟩
    rw [h]
    by_cases hνμ : ν = μ
    · subst hνμ; simp
    · rw [if_neg (fun e => hνμ (congrArg Subtype.val e)), if_neg hνμ, Int.cast_zero]
  · rw [EKCenterPower.orth hd (mem_degreePiece_card ν)
      (EKDualBases.fBasis μ.card ⟨μ, rfl⟩).2, Int.cast_zero, if_neg]
    rintro rfl; exact hd rfl

theorem fK_linearIndependent : LinearIndependent k (fK k) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  ext ν
  have h := congrArg (quotientForm (-1 : k) (eBasisK ν)) hl
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_zero] at h
  simp only [map_smul, form_eBasisK_fK, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  rw [Finsupp.sum_ite_eq] at h
  split_ifs at h with hν
  · exact h
  · simpa using hν

theorem hBasisK_mem_span_fK (ν : YoungDiagram) :
    hBasisK (k := k) ν ∈ Submodule.span k (Set.range (fK k)) := by
  have h := EKDualBases.h_eq_M_f ν.card ⟨ν, rfl⟩
  have h' := congrArg (fun x : EKIntegralBases.degreePiece ν.card => psiRing (k := k) (x : QZ)) h
  simp only [EKIntegralBases.degreeHBasis_apply, Submodule.coe_sum, Submodule.coe_smul,
    map_sum, psiRing_zsmul] at h'
  rw [hBasisK_eq_psiRing, h']
  refine Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _ ?_
  rw [← fK_shape]
  exact Submodule.subset_span ⟨μ.val, rfl⟩

theorem fK_span : Submodule.span k (Set.range (fK k)) = ⊤ := by
  rw [eq_top_iff, ← (hBasisK (k := k)).span_eq, Submodule.span_le]
  rintro _ ⟨ν, rfl⟩
  exact hBasisK_mem_span_fK ν

variable (k) in
/-- **EK §3.1 over `k`:** the odd forgotten functions `{f_λ}` form a `k`-basis of `Λ_k`. -/
def fBasisK : Basis YoungDiagram k (LamK k) :=
  Basis.mk fK_linearIndependent (by rw [fK_span])

@[simp] theorem fBasisK_apply (μ : YoungDiagram) : fBasisK k μ = fK k μ := by
  simp [fBasisK]

/-! ## The odd Schur basis `{s_λ}` over `k` -/

variable (k) in
/-- `s_λ ∈ Λ_k`, the image of the integral odd Schur function (EK (3.6)). -/
def sK (μ : YoungDiagram) : LamK k :=
  psiRing ((EKOddRSKII.schur μ.card ⟨μ, rfl⟩ : EKIntegralBases.degreePiece μ.card) : QZ)

theorem sK_shape {d : ℕ} (μ : DegreeShape d) :
    sK k μ.val = psiRing ((EKOddRSKII.schur d μ : EKIntegralBases.degreePiece d) : QZ) := by
  obtain ⟨μ, rfl⟩ := μ
  rfl

/-- **EK Cor. 3.9, (3.11), over `k`:** `(s_λ, s_μ) = (-1)^{C(λᵀ,2)} δ_{λμ}`. -/
theorem corollary_3_9_K (lam μ : YoungDiagram) :
    quotientForm (-1 : k) (sK k lam) (sK k μ) =
      if lam = μ then (-1 : k) ^ EKSchurOrthonormalControls.transposeChoose lam else 0 := by
  rw [sK, sK, form_psiRing]
  by_cases hd : lam.card = μ.card
  · have h := EKClosureComposition.corollary_3_9 μ.card ⟨lam, hd⟩ ⟨μ, rfl⟩
    have hs : (EKOddRSKII.schur lam.card ⟨lam, rfl⟩ : QZ) =
        (EKSchurOrthonormal.schur μ.card ⟨lam, hd⟩ : QZ) := by
      have : ∀ {d e : ℕ} (he : d = e) (lam : YoungDiagram) (h1 : lam.card = d) (h2 : lam.card = e),
          (EKOddRSKII.schur d ⟨lam, h1⟩ : QZ) = (EKSchurOrthonormal.schur e ⟨lam, h2⟩ : QZ) := by
        rintro d e rfl lam h1 h2; rfl
      exact this hd lam rfl hd
    rw [hs]
    change ((EKRadicalQuotient.quotientPairing (EKSchurOrthonormal.schur μ.card ⟨lam, hd⟩ : QZ)
      (EKSchurOrthonormal.schur μ.card ⟨μ, rfl⟩ : QZ) : ℤ) : k) = _
    rw [h]
    by_cases hlm : lam = μ
    · subst hlm; simp
    · rw [if_neg (fun e => hlm (congrArg Subtype.val e)), if_neg hlm, Int.cast_zero]
  · rw [EKCenterPower.orth hd (EKOddRSKII.schur lam.card ⟨lam, rfl⟩).2
      (EKOddRSKII.schur μ.card ⟨μ, rfl⟩).2, Int.cast_zero, if_neg]
    rintro rfl; exact hd rfl

theorem sK_linearIndependent : LinearIndependent k (sK k) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  ext ν
  have h := congrArg (quotientForm (-1 : k) (sK k ν)) hl
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_zero] at h
  simp only [map_smul, corollary_3_9_K, smul_eq_mul, mul_ite, mul_zero] at h
  rw [Finsupp.sum_ite_eq] at h
  split_ifs at h with hν
  · have hu : IsUnit ((-1 : k) ^ EKSchurOrthonormalControls.transposeChoose ν) :=
      (isUnit_neg_one (α := k)).pow _
    exact (hu.mul_left_eq_zero).mp h
  · simpa using hν

/-- **EK (3.6) over `k`:** `h_μ = Σ_λ K_{λμ}^{±} s_λ` (the signed odd Kostka numbers). -/
theorem hBasisK_eq_sum_sK {d : ℕ} (μ : DegreeShape d) :
    hBasisK (k := k) μ.val =
      ∑ lam : DegreeShape d, ((TableauDominance.signedKostka lam.val μ.val : ℤ) : k) • sK k lam.val := by
  have h := congrArg (psiRing (k := k)) (EKOddRSKII.schur_defining d μ)
  rw [map_sum] at h
  rw [hBasisK_eq_psiRing, h]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [psiRing_zsmul, sK_shape]

theorem sK_span : Submodule.span k (Set.range (sK k)) = ⊤ := by
  rw [eq_top_iff, ← (hBasisK (k := k)).span_eq, Submodule.span_le]
  rintro _ ⟨ν, rfl⟩
  change hBasisK (⟨ν, rfl⟩ : DegreeShape ν.card).val ∈ _
  rw [hBasisK_eq_sum_sK]
  exact Submodule.sum_mem _ fun lam _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨lam.val, rfl⟩)

variable (k) in
/-- **EK §3.3 over `k`:** the odd Schur functions `{s_λ}` form a `k`-basis of `Λ_k`. -/
def sBasisK : Basis YoungDiagram k (LamK k) :=
  Basis.mk sK_linearIndependent (by rw [sK_span])

@[simp] theorem sBasisK_apply (μ : YoungDiagram) : sBasisK k μ = sK k μ := by
  simp [sBasisK]

/-! ## Lemma 3.11 over `k` -/

/-- **EK Lemma 3.11, (3.13), over every commutative ring `k`:**
`ψ₁ψ₂(s_λ) = (-1)^{ℓ(w_λ)+|λ|} s_{λᵀ}`. -/
theorem lemma_3_11_K (lam : YoungDiagram) :
    psi12K k (sK k lam) =
      ((-1 : k) ^ (EKSemiorthogonality.ell lam + lam.card)) • sK k lam.transpose := by
  have h := congrArg (psiRing (k := k)) (EKFinalClosure.lemma_3_11 lam.card ⟨lam, rfl⟩)
  rw [sK, psi12K_psiRing, h, psiRing_zsmul]
  push_cast
  congr 1
  have := sK_shape (k := k) (EKDualBases.transposeShape lam.card ⟨lam, rfl⟩)
  exact this.symm

end OddMath.Frontier.EKOverK

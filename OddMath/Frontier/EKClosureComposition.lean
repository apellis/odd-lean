import OddMath.Frontier.EKClosureCompositionControls

/-!
# EK1107.5610v2 §3.3 closure composition: Cor 3.8/3.9, Prop 3.10 unconditional; Cor 3.12/3.13
# conditional on (3.13) only

Pure composition of existing main modules; every mismatch is bridged by a proved lemma in
`EKClosureCompositionControls`.

(a) `identity39` : `EKSchurOrthonormal.Identity39 d` for EVERY d, from the existing all-degree
    EK (3.9) theorem `EKKostkaValues.Mh_eq_sum_kostka` and the proved sign bridge
    `sign_directNorth_eq_evenParts`.  Hence `corollary_3_8` (EK (3.10)) and `corollary_3_9`
    (EK (3.11)) hold unconditionally in every degree.
(b) `identity311` : `EKProp310.Identity311 d` for every d, from (a) (the hypothesis is literally
    the (3.11) statement with the proved-equal `schur`/`transposeChoose`).  Hence
    `proposition_3_10` and `proposition_3_10_normalisation` are unconditional.
(c) `cor_3_12_first_iff_lemma_3_11` : (3.14, first) ⟺ (3.13) in every degree, unconditionally;
    `cor_3_12_first` : (3.14, first) from (3.13)_d, the SOLE hypothesis.
(d) `cor39` discharges the (3.11) hypothesis of `EKOddRSKII`; `cor_3_12_second` and
    `cor_3_13` hold with (3.13)_d as the SOLE hypothesis.  Also the full equivalence package
    `equivalences` (every degree, unconditional).

(3.13) (EK Lemma 3.11) itself is NOT proved here (it is proved in `EKLemma311Cond`; see `EKFinalClosure`).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKClosureComposition
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKClosureCompositionControls
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## (a) EK (3.9) in the `EKSchurOrthonormal` form, every degree; Cor 3.8, Cor 3.9 -/

/-- EK (3.9), exactly `EKSchurOrthonormal.Identity39 d`, for every degree d. -/
theorem identity39 (d : ℕ) : EKSchurOrthonormal.Identity39 d := by
  intro μ ρ
  rw [EKKostkaValues.Mh_eq_sum_kostka]
  apply Finset.sum_congr rfl
  intro lam _
  rw [sign_directNorth_eq_evenParts]

/-- EK Corollary 3.8, (3.10): `(-1)^{C(λᵀ,2)} s_λ = Σ_μ K_{λμ} m_μ`, every degree, unconditional. -/
theorem corollary_3_8 (d : ℕ) (lam : DegreeShape d) :
    (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam.val • EKSchurOrthonormal.schur d lam =
      ∑ μ, signedKostka lam.val μ.val • mBasis d μ :=
  EKSchurOrthonormal.corollary_3_8 d (identity39 d) lam

/-- EK Corollary 3.9, (3.11): `(s_λ, s_μ) = (-1)^{C(λᵀ,2)} δ_{λμ}`, every degree, unconditional. -/
theorem corollary_3_9 (d : ℕ) (lam μ : DegreeShape d) :
    quotientPairing (EKSchurOrthonormal.schur d lam : Q) (EKSchurOrthonormal.schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam.val else 0 :=
  EKSchurOrthonormal.corollary_3_9 d (identity39 d) lam μ

/-! ## (b) Identity311 discharged; Prop 3.10 unconditional -/

/-- The `EKProp310` hypothesis (3.11), for every degree d. -/
theorem identity311 (d : ℕ) : EKProp310.Identity311 d := by
  intro lam μ
  rw [schur_prop310_eq, transposeChoose_prop310_eq]
  exact corollary_3_9 d lam μ

/-- EK Proposition 3.10, every degree, unconditional: `s'_λ` exists uniquely and equals
`(-1)^{ℓ(w_λ)+C(λᵀ,2)} s_λ`. -/
theorem proposition_3_10 (d : ℕ) (lam : DegreeShape d) :
    (∃! x : degreePiece d, EKProp310.IsSPrime d lam x) ∧
    ∀ x : degreePiece d, EKProp310.IsSPrime d lam x →
      x = (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + EKProp310Controls.transposeChoose lam.val) •
        EKProp310.schur d lam :=
  EKProp310.proposition_3_10 d (identity311 d) lam

/-- Prop 3.10 normalisation (single column: `s'_{(1^d)} = e_d`), every degree, unconditional. -/
theorem proposition_3_10_normalisation (d : ℕ) (lam : DegreeShape d)
    (hcol : lam.val.transpose.rowLens = [d]) :
    ((EKProp310.sgn lam.val • EKProp310.schur d lam : degreePiece d) : Q) =
      EKElementaryQuotient.e d :=
  EKProp310.proposition_3_10_normalisation d (identity311 d) lam hcol

/-! ## (c) Cor 3.12 first equation ⟺ Lemma 3.11 (3.13) -/

/-- (3.14, first) ⟺ (3.13), every degree (unconditional equivalence). -/
theorem cor_3_12_first_iff_lemma_3_11 (d : ℕ) :
    EKOddRSKII.First312 d ↔ EKOddRSKII.Lemma311 d :=
  EKOddRSKII.first312_iff_lemma311 d

/-- Cor 3.12 first equation, with (3.13)_d as the SOLE hypothesis. -/
theorem cor_3_12_first (d : ℕ) (h313 : EKOddRSKII.Lemma311 d) : EKOddRSKII.First312 d :=
  (cor_3_12_first_iff_lemma_3_11 d).2 h313

/-! ## (d) Cor 3.12 second equation and Cor 3.13, (3.11) discharged -/

/-- The `EKOddRSKII` hypothesis (3.11), for every degree d. -/
theorem cor39 (d : ℕ) : EKOddRSKII.Cor39 d := by
  intro lam μ
  rw [schur_oddRSKII_eq, transposeChoose_oddRSKII_eq]
  exact corollary_3_9 d lam μ

/-- Cor 3.12 second equation (3.14, second), with (3.13)_d as the SOLE hypothesis. -/
theorem cor_3_12_second (d : ℕ) (h313 : EKOddRSKII.Lemma311 d) : EKOddRSKII.Second312 d :=
  EKOddRSKII.CONDITIONAL_cor_3_12_second d h313 (cor39 d)

/-- Cor 3.13 (3.15), both printed equalities, with (3.13)_d as the SOLE hypothesis. -/
theorem cor_3_13 (d : ℕ) (h313 : EKOddRSKII.Lemma311 d) : EKOddRSKII.OddRSKII d :=
  EKOddRSKII.CONDITIONAL_cor_3_13 d h313 (cor39 d)

/-- The existing equivalence package with (3.11) discharged: every degree, unconditional. -/
theorem equivalences (d : ℕ) :
    (EKOddRSKII.Lemma311 d ↔ EKOddRSKII.First312 d) ∧
    (EKOddRSKII.First312 d ↔ EKOddRSKII.Second312 d) ∧
    (EKOddRSKII.Second312 d ↔ EKOddRSKII.DualRSK d) ∧
    (EKOddRSKII.First312 d → EKOddRSKII.OddRSKII d) :=
  EKOddRSKII.equivalences_of_cor39 d (cor39 d)

end OddMath.Frontier.EKClosureComposition

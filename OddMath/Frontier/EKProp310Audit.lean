import OddMath.Frontier.EKProp310

/-! Post-production audit for `EKProp310` (EK1107.5610v2 Proposition 3.10, printed p29).

* Axiom footprint of every headline theorem (no `sorryAx`, no `native_decide`/`ofReduceBool`).
* Statement pins: the definitions `IsSPrime`, `Identity311`, `sgn` unfold to the literal
  source statements (by `Iff.rfl`/`rfl`), and the `ℓ(w_λ)` factor is the existing
  `EKDualBases.triangularMatrix_diag` sign / source (2.21).
* Consumers: the production `s'_λ = sgn(λ) • s_λ` agrees with the PRE-registered hand
  values `EKProp310Controls.sp…` for every |λ| ≤ 3, and the production uniqueness rejects
  the wrong-sign candidates (sign without `ℓ(w_λ)` at λ = (2,1); without `C(λᵀ,2)` at
  λ = (1,1)).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKProp310Audit
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition ePartition)
open EKProp310Controls (evenParts transposeChoose sh1 sh2 sh11 sh3 sh21 sh111)
open EKProp310
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

#print axioms EKProp310.proposition_3_10
#print axioms EKProp310.proposition_3_10_le_four
#print axioms EKProp310.proposition_3_10_iff_identity311
#print axioms EKProp310.proposition_3_10_normalisation
#print axioms EKProp310.identity311_le_four
#print axioms EKProp310.schur_val_unique
#print axioms EKProp310.identity311_of_isSPrime
#print axioms EKProp310.eAbove_restricted_nondeg
#print axioms EKProp310.pair_schur_e_vanish
#print axioms EKProp310.dom_transpose
#print axioms EKProp310Controls.sp_unique
#print axioms EKProp310Controls.drop_ell_rejected

/-! ## Statement pins -/

open Classical in
/-- The two defining properties, literally. -/
example (d : ℕ) (lam : DegreeShape d) (x : degreePiece d) :
    IsSPrime d lam x ↔
      ((∀ μ : DegreeShape d, lam.val.transpose.rowLens < μ.val.rowLens →
          quotientPairing (x : Q) (ePartition μ.val) = 0) ∧
       ∃ b : DegreeShape d → ℤ, x = degreeEBasis d (transposeShape d lam) +
         ∑ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => LexLT lam.val.transpose μ.val),
           b μ • degreeEBasis d μ) := Iff.rfl

/-- The hypothesis is exactly the `EKSchurOrthonormal.corollary_3_9` conclusion (3.11). -/
example (d : ℕ) : Identity311 d ↔ ∀ lam μ : DegreeShape d,
    quotientPairing (schur d lam : Q) (schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := Iff.rfl

/-- `s_λ` is the (3.6) solution with the literal odd Kostka numbers (3.7). -/
example (d : ℕ) (μ : DegreeShape d) :
    degreeHBasis d μ = ∑ lam, signedKostka lam.val μ.val • schur d lam := schur_defining d μ

/-- The Proposition 3.10 sign. -/
example (lam : YoungDiagram) :
    sgn lam = (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + transposeChoose lam) := rfl

/-- The `ℓ(w_λ)` factor is the existing `triangularMatrix_diag` sign, i.e. source (2.21)
`(h_λ, e_{λᵀ}) = (-1)^{ℓ(w_λ)}`. -/
theorem ell_is_triangular_diag (d : ℕ) (lam : DegreeShape d) :
    quotientPairing (hPartition lam.val) (ePartition lam.val.transpose) = triangularMatrix d lam lam ∧
    triangularMatrix d lam lam = (-1 : ℤ) ^ EKSemiorthogonality.ell lam.val :=
  ⟨by rw [triangularMatrix_diag]; exact pair_h_e_diag lam.val, triangularMatrix_diag d lam⟩

/-! ## Consumers: production agrees with the pre-registered hand values, |λ| ≤ 3 -/

theorem schur1 (lam : DegreeShape 1) : (schur 1 lam : Q) = EKProp310Controls.hand1 lam :=
  schur_val_unique 1 _ EKProp310Controls.hand1_defining lam
theorem schur2 (lam : DegreeShape 2) : (schur 2 lam : Q) = EKProp310Controls.hand2 lam :=
  schur_val_unique 2 _ EKProp310Controls.hand2_defining lam
theorem schur3 (lam : DegreeShape 3) : (schur 3 lam : Q) = EKProp310Controls.hand3 lam :=
  schur_val_unique 3 _ EKProp310Controls.hand3_defining lam

/-- Production `s'_λ = sgn(λ) • s_λ` equals the hand values `sp…` for every |λ| ≤ 3. -/
theorem production_matches_hand :
    ((sgn sh1.val • schur 1 sh1 : degreePiece 1) : Q) = EKProp310Controls.sp1 ∧
    ((sgn sh2.val • schur 2 sh2 : degreePiece 2) : Q) = EKProp310Controls.sp2 ∧
    ((sgn sh11.val • schur 2 sh11 : degreePiece 2) : Q) = EKProp310Controls.sp11 ∧
    ((sgn sh3.val • schur 3 sh3 : degreePiece 3) : Q) = EKProp310Controls.sp3 ∧
    ((sgn sh21.val • schur 3 sh21 : degreePiece 3) : Q) = EKProp310Controls.sp21 ∧
    ((sgn sh111.val • schur 3 sh111 : degreePiece 3) : Q) = EKProp310Controls.sp111 := by
  obtain ⟨h1, h2, h11, h3, h21, h111⟩ := EKProp310Controls.sp_eq_sign_hand
  simp only [Submodule.coe_smul, schur1, schur2, schur3, sgn]
  exact ⟨h1.symm, h2.symm, h11.symm, h3.symm, h21.symm, h111.symm⟩

/-- The production theorem, instantiated: `s'_(2,1) = s_(2,1)` and `s'_(1,1,1) = -s_(1,1,1)`. -/
theorem instances :
    (∀ x, IsSPrime 3 sh21 x → x = schur 3 sh21) ∧
    (∀ x, IsSPrime 3 sh111 x → x = -schur 3 sh111) := by
  have s := EKProp310Controls.predicted_signs
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [(proposition_3_10_le_four 3 (by norm_num) sh21).2 x hx, s.2.2.2.2.1, one_smul]
  · rw [(proposition_3_10_le_four 3 (by norm_num) sh111).2 x hx, s.2.2.2.2.2, neg_one_smul]

/-- A nonzero `s_λ` cannot equal its own negative (torsion-free check via the Gram norm). -/
theorem schur_ne_neg (d : ℕ) (hd : d ≤ 4) (lam : DegreeShape d) : schur d lam ≠ -schur d lam := by
  intro h
  have h311 := identity311_le_four d hd lam lam
  rw [if_pos rfl] at h311
  have h2 := congrArg (fun z : degreePiece d => quotientPairing (schur d lam : Q) (z : Q)) h
  simp only [Submodule.coe_neg, map_neg] at h2
  rw [h311] at h2
  have hsq := sign_mul_self (transposeChoose lam.val)
  have : (-1 : ℤ) ^ transposeChoose lam.val = 0 := by linarith
  rw [this, zero_mul] at hsq
  exact zero_ne_one hsq

/-- Production rejects dropping `ℓ(w_λ)` at λ = (2,1): `(-1)^{C(λᵀ,2)} s_(2,1)` is NOT `s'_(2,1)`. -/
theorem production_rejects_drop_ell :
    ¬ IsSPrime 3 sh21 ((-1 : ℤ) ^ transposeChoose sh21.val • schur 3 sh21) := by
  intro h
  have := instances.1 _ h
  rw [EKProp310Controls.sh21_signs.1, pow_one, neg_one_smul] at this
  exact schur_ne_neg 3 (by norm_num) sh21 this.symm

/-- Production rejects dropping `C(λᵀ,2)` at λ = (1,1): `(-1)^{ℓ(w_λ)} s_(1,1)` is NOT `s'_(1,1)`. -/
theorem production_rejects_drop_choose :
    ¬ IsSPrime 2 sh11 ((-1 : ℤ) ^ EKSemiorthogonality.ell sh11.val • schur 2 sh11) := by
  intro h
  have := (proposition_3_10_le_four 2 (by norm_num) sh11).2 _ h
  rw [EKProp310Controls.predicted_signs.2.2.1, EKProp310Controls.ell_values.2.2.1, pow_zero,
    one_smul, neg_one_smul] at this
  exact schur_ne_neg 2 (by norm_num) sh11 this

end OddMath.Frontier.EKProp310Audit

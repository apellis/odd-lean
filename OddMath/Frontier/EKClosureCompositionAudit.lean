import OddMath.Frontier.EKClosureComposition

/-! Post-production audit for `EKClosureComposition`.

* Axiom footprint of every headline theorem (expected: at most `propext`, `Classical.choice`,
  `Quot.sound`; no placeholder or `ofReduceBool` axiom).
* Statement exhibits: each headline is restated verbatim as an `example` whose ONLY binders are
  the degree/indices and, for (c)/(d), the single hypothesis `EKOddRSKII.Lemma311 d`, which is
  pinned by `Iff.rfl` to the printed (3.13).  The hypothesis predicates that were discharged
  (`Identity39`, `Identity311`, `Cor39`) are pinned by `Iff.rfl` to their literal (3.9)/(3.11)
  statements, and exhibited in a degree (d = 5, 7) outside every earlier finite discharge (d ≤ 4).
* Consumers: the unconditional Cor 3.9 reproduces the pre-registered hand-computed degree-2 norms
  (`EKSchurOrthonormal.degree_two_schur_norms`: +1 for (2), −1 for (1,1)), and the existing
  sign-dropping control (`EKSchurOrthonormalControls`, unsigned (3.9) rejected at d = 2) still
  stands against the now-unconditional signed (3.9).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKClosureCompositionAudit
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKClosureComposition EKClosureCompositionControls
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Axiom footprint -/

#print axioms EKClosureComposition.identity39
#print axioms EKClosureComposition.corollary_3_8
#print axioms EKClosureComposition.corollary_3_9
#print axioms EKClosureComposition.identity311
#print axioms EKClosureComposition.proposition_3_10
#print axioms EKClosureComposition.proposition_3_10_normalisation
#print axioms EKClosureComposition.cor_3_12_first_iff_lemma_3_11
#print axioms EKClosureComposition.cor_3_12_first
#print axioms EKClosureComposition.cor39
#print axioms EKClosureComposition.cor_3_12_second
#print axioms EKClosureComposition.cor_3_13
#print axioms EKClosureComposition.equivalences
#print axioms EKClosureCompositionControls.sign_directNorth_eq_evenParts
#print axioms EKClosureCompositionControls.sign_bridge_is_parity_only
#print axioms EKClosureCompositionControls.schur_prop310_eq
#print axioms EKClosureCompositionControls.schur_oddRSKII_eq

/-! ## Pins: discharged predicates are the literal source statements -/

/-- (3.9), printed sign `(-1)^{λ₂+λ₄+⋯}`, source `M′ = (h,h)`. -/
example (d : ℕ) : EKSchurOrthonormal.Identity39 d ↔ ∀ μ ρ : DegreeShape d,
    Mh d μ ρ = ∑ lam : DegreeShape d, (-1 : ℤ) ^ EKSchurOrthonormalControls.evenParts lam.val.rowLens *
      signedKostka lam.val μ.val * signedKostka lam.val ρ.val := Iff.rfl

/-- The `EKProp310` hypothesis is (3.11). -/
example (d : ℕ) : EKProp310.Identity311 d ↔ ∀ lam μ : DegreeShape d,
    quotientPairing (EKProp310.schur d lam : Q) (EKProp310.schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ EKProp310Controls.transposeChoose lam.val else 0 := Iff.rfl

/-- The `EKOddRSKII` (3.11) hypothesis is (3.11). -/
example (d : ℕ) : EKOddRSKII.Cor39 d ↔ ∀ lam μ : DegreeShape d,
    quotientPairing (EKOddRSKII.schur d lam : Q) (EKOddRSKII.schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ EKOddRSKIIControls.transposeChoose lam.val else 0 := Iff.rfl

/-- The SOLE remaining hypothesis of (c)/(d) is printed (3.13):
`ψ₁ψ₂(s_λ) = (-1)^{ℓ(w_λ)+|λ|} s_{λᵀ}`. -/
example (d : ℕ) : EKOddRSKII.Lemma311 d ↔ ∀ lam : DegreeShape d,
    EKAutomorphisms.psi12 (EKOddRSKII.schur d lam : Q) =
      ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card)) •
        (EKOddRSKII.schur d (transposeShape d lam) : Q) := Iff.rfl

/-! ## Headline exhibits: no residual hypothesis beyond those allowed -/

-- (a) unconditional, every degree
example : ∀ d : ℕ, EKSchurOrthonormal.Identity39 d := identity39
example : ∀ (d : ℕ) (lam : DegreeShape d),
    (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam.val • EKSchurOrthonormal.schur d lam =
      ∑ μ, signedKostka lam.val μ.val • mBasis d μ := corollary_3_8
example : ∀ (d : ℕ) (lam μ : DegreeShape d),
    quotientPairing (EKSchurOrthonormal.schur d lam : Q) (EKSchurOrthonormal.schur d μ : Q) =
      if lam = μ then (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam.val else 0 :=
  corollary_3_9
-- (b) unconditional, every degree
example : ∀ d : ℕ, EKProp310.Identity311 d := identity311
example : ∀ (d : ℕ) (lam : DegreeShape d),
    (∃! x : degreePiece d, EKProp310.IsSPrime d lam x) ∧
    ∀ x : degreePiece d, EKProp310.IsSPrime d lam x →
      x = (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + EKProp310Controls.transposeChoose lam.val) •
        EKProp310.schur d lam := proposition_3_10
example : ∀ (d : ℕ) (lam : DegreeShape d), lam.val.transpose.rowLens = [d] →
    ((EKProp310.sgn lam.val • EKProp310.schur d lam : degreePiece d) : Q) =
      EKElementaryQuotient.e d := proposition_3_10_normalisation
-- (c) equivalence unconditional; first equation conditional on (3.13) only
example : ∀ d : ℕ, EKOddRSKII.First312 d ↔ EKOddRSKII.Lemma311 d := cor_3_12_first_iff_lemma_3_11
example : ∀ d : ℕ, EKOddRSKII.Lemma311 d → EKOddRSKII.First312 d := cor_3_12_first
-- (d) (3.11) discharged; conditional on (3.13) only
example : ∀ d : ℕ, EKOddRSKII.Cor39 d := cor39
example : ∀ d : ℕ, EKOddRSKII.Lemma311 d → EKOddRSKII.Second312 d := cor_3_12_second
example : ∀ d : ℕ, EKOddRSKII.Lemma311 d → EKOddRSKII.OddRSKII d := cor_3_13

-- beyond every earlier finite discharge (d ≤ 4)
example : EKSchurOrthonormal.Identity39 5 := identity39 5
example : EKProp310.Identity311 7 := identity311 7
example : EKOddRSKII.Cor39 6 := cor39 6

/-! ## Consumers -/

/-- The unconditional Cor 3.9 gives `(s_{11}, s_{11}) = -1` and `(s_2, s_2) = +1`, agreeing with
the pre-registered hand computation `EKSchurOrthonormal.degree_two_schur_norms`. -/
theorem degree_two_norms_agree :
    quotientPairing (EKSchurOrthonormal.schur 2 EKSchurOrthonormalControls.sh11 : Q)
        (EKSchurOrthonormal.schur 2 EKSchurOrthonormalControls.sh11 : Q) = -1 ∧
    quotientPairing (EKSchurOrthonormal.schur 2 EKSchurOrthonormalControls.sh2 : Q)
        (EKSchurOrthonormal.schur 2 EKSchurOrthonormalControls.sh2 : Q) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [corollary_3_9, if_pos rfl, EKSchurOrthonormalControls.sh11_signs.1]; norm_num
  · rw [corollary_3_9, if_pos rfl, EKSchurOrthonormalControls.sh2_signs.1]; norm_num

/-- Independent confirmation: the hand-computed norms coincide with the composed theorem. -/
theorem composed_matches_hand :
    (if EKSchurOrthonormalControls.sh11 = EKSchurOrthonormalControls.sh11 then
        (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose EKSchurOrthonormalControls.sh11.val
      else 0) =
      quotientPairing (EKSchurOrthonormal.schur 2 EKSchurOrthonormalControls.sh11 : Q)
        (EKSchurOrthonormal.schur 2 EKSchurOrthonormalControls.sh11 : Q) := by
  rw [EKSchurOrthonormal.degree_two_schur_norms.2.1, if_pos rfl,
    EKSchurOrthonormalControls.sh11_signs.1]; norm_num

end OddMath.Frontier.EKClosureCompositionAudit

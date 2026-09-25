import OddMath.Frontier.EKLemma311Cond

/-! Audit of `EKLemma311Cond`.
Restates the target with fully qualified names (definitional identity check), then prints the
axiom closure of every owned declaration.  Allowed: propext, Classical.choice, Quot.sound. -/

namespace OddMath.Frontier.EKLemma311CondAudit
open OddMath.Frontier
noncomputable local instance (d : ℕ) : Fintype (DegreeShapes.DegreeShape d) := DegreeShapes.degreeFintype d
noncomputable local instance (d : ℕ) : DecidableEq (DegreeShapes.DegreeShape d) := Classical.decEq _

/-- The exact conditional target, restated with qualified names. -/
theorem target :
    ∀ d : ℕ, EKLemma311CondControls.Identity311 d →
      ∀ lam : DegreeShapes.DegreeShape d,
        EKAutomorphisms.psi12
            ((KostkaModuleInversion.recover d (EKIntegralBases.degreeHBasis d) lam :
              EKIntegralBases.degreePiece d) : EKRadicalQuotient.Q) =
          ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + lam.val.card)) •
            ((KostkaModuleInversion.recover d (EKIntegralBases.degreeHBasis d)
                (EKDualBases.transposeShape d lam) :
              EKIntegralBases.degreePiece d) : EKRadicalQuotient.Q) :=
  fun d h lam => EKLemma311Cond.lemma_3_11_of_identity311 d h lam

end OddMath.Frontier.EKLemma311CondAudit

#print axioms OddMath.Frontier.EKLemma311CondAudit.target
#print axioms OddMath.Frontier.EKLemma311Cond.lemma_3_11_of_identity311
#print axioms OddMath.Frontier.EKLemma311Cond.pair_schur_psi12_schur
#print axioms OddMath.Frontier.EKLemma311Cond.sign_identity
#print axioms OddMath.Frontier.EKLemma311Cond.wordSign_eq
#print axioms OddMath.Frontier.EKLemma311Cond.pair_psi12_up
#print axioms OddMath.Frontier.EKLemma311Cond.pair_psi12_eAbove
#print axioms OddMath.Frontier.EKLemma311Cond.pair_schur_h
#print axioms OddMath.Frontier.EKLemma311Cond.pair_schur_e_dom
#print axioms OddMath.Frontier.EKLemma311Cond.pair_h_e_dom
#print axioms OddMath.Frontier.EKLemma311Cond.gale_ryser
#print axioms OddMath.Frontier.EKLemma311Cond.expansion
#print axioms OddMath.Frontier.EKLemma311Cond.schur_sub_e_mem
#print axioms OddMath.Frontier.EKLemma311Cond.schur_sub_mem_upS
#print axioms OddMath.Frontier.EKLemma311CondControls.wrong_sign_refuted
#print axioms OddMath.Frontier.EKLemma311CondControls.printed_sign_at_one

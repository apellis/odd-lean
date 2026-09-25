import OddMath.Frontier.CyclotomicMatrix
import OddMath.Frontier.OddGrassmannSchur
import OddMath.Frontier.OddSymmetricLimit
import OddMath.Frontier.CyclotomicGraded

/-! Audit for EKL arXiv:1111.1320v1 §5: headline statements with transitive axioms. -/
namespace OddMath.Frontier.CyclotomicAudit

/-- Prop 5.2: `ONH_a^N ≅ Mat_{a!}(OH_{a,N})` (ungraded). -/
noncomputable example (n N : ℕ) :
    Cyclotomic.ONH n N ≃+* Matrix (NilCoxeterWords.Perm n) (NilCoxeterWords.Perm n)
      (Cyclotomic.OH n N) :=
  Cyclotomic.prop_5_2 n N

/-- Prop 5.4: `OH_{a,N}` is free over `ℤ` of rank `C(N, a)`. -/
example (n b : ℕ) :
    Module.finrank ℤ (Cyclotomic.OH n (n+2+b)) = (n+2+b).choose (n+2) :=
  OddGrassmannSchur.finrank_OH n b

#print axioms Cyclotomic.prop_5_2
#print axioms Cyclotomic.entryIdeal_eq_rev
#print axioms Cyclotomic.lemma_5_1
#print axioms Cyclotomic.lemma_5_1_left
#print axioms Cyclotomic.lemma_5_1_printed_false
#print axioms Cyclotomic.eq_5_8_false
#print axioms Cyclotomic.eq_5_9_false
#print axioms Cyclotomic.eq_5_9_top
#print axioms Cyclotomic.supercentral_inverse
#print axioms Cyclotomic.span_grassmannRelations
#print axioms Cyclotomic.OH_self_equiv
#print axioms OddSymmetricLimit.equation_5_3
#print axioms OddSymmetricLimit.inverse_limit
#print axioms OddGrassmannSchur.conjecture_5_3
#print axioms OddGrassmannSchur.proposition_5_4
#print axioms OddGrassmannSchur.finrank_OH

#print axioms Cyclotomic.prop_5_2_degree_iff
#print axioms Cyclotomic.ohConnected
#print axioms Cyclotomic.onhCycK0Equiv
#print axioms Cyclotomic.finrank_K0Cyc

end OddMath.Frontier.CyclotomicAudit

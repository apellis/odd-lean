import OddMath.PbwL3
import OddMath.Frontier.PbwEquivalence
import OddMath.Frontier.NilHeckeGradedEnd

/-! EKL1111.1320v1 small-rank boundary controls (N = 0, N = 1).

Existing-behavior hand checks, compiled BEFORE any new production module.
N = 0: empty generator set, no relators. N = 1: single dot generator, no
crossings; relator hypotheses are vacuous, the diagonal square does not vanish.
Every statement below uses only inherited modules. -/
namespace OddMath.Frontier.NilHeckeSmallRankControls

open scoped BigOperators

/-- N = 0: no relator words over the empty generator set. -/
theorem relSet_empty_zero : OddMath.PbwL2.relSet 0 = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro w hw
  obtain ⟨i, _, _, _⟩ := hw
  exact i.elim0

/-- N = 0: no relator index pairs. -/
theorem relPairs_empty_zero : OddMath.PbwL2.relPairs 0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x _
  exact x.1.elim0

/-- N = 0: every exponent vector has polynomial degree zero. -/
theorem pdegree_zero_all (a : Fin 0 → ℕ) :
    OddMath.Frontier.NilHeckeGradedEnd.pdegree a = 0 := by
  have hU : (Finset.univ : Finset (Fin 0)) = ∅ :=
    Finset.eq_empty_iff_forall_not_mem.mpr fun i _ => i.elim0
  simp [OddMath.Frontier.NilHeckeGradedEnd.pdegree, hU]

/-- N = 1: no relator words; every alleged relator needs distinct generators. -/
theorem relSet_empty_one : OddMath.PbwL2.relSet 1 = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro w hw
  obtain ⟨i, j, h, _⟩ := hw
  exact h (Subsingleton.elim i j)

/-- N = 1: no relator index pairs. -/
theorem relPairs_empty_one : OddMath.PbwL2.relPairs 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x hx
  rw [OddMath.PbwL2.relPairs] at hx
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and] at hx
  exact hx (Subsingleton.elim x.1 x.2)

/-- N = 1 negative control: there are no two distinct dot generators,
so no crossing/anticommutator relator can fire. -/
theorem no_distinct_generators_one : ¬ ∃ i j : Fin 1, i ≠ j :=
  fun ⟨i, j, h⟩ => h (Subsingleton.elim i j)

/-- N = 1 must-hold control: the single generator square does not vanish. -/
theorem single_square_ne_zero (i : Fin 1) :
    OddMath.PbwL3.Phi 1
      (OddMath.PbwL2.q 1 i * OddMath.PbwL2.q 1 i) ≠ 0 :=
  OddMath.PbwL3.Phi_sq_ne_zero 1 i

/-- N = 1 must-fail control (Phi image): the diagonal anticommutator maps to
twice the generator square, i.e. the doubled monomial with coefficient 2,
which is nonzero. -/
theorem diagonal_image_ne_zero (i : Fin 1) :
    OddMath.PbwL3.Phi 1 (OddMath.PbwL2.q 1 i * OddMath.PbwL2.q 1 i +
      OddMath.PbwL2.q 1 i * OddMath.PbwL2.q 1 i) ≠ 0 := by
  rw [map_add, OddMath.PbwL3.Phi_sq_form,
    OddMath.SkewPolynomial.generator_square]
  have h2 : OddMath.SkewPolynomial.monomial
      (OddMath.SkewPolynomial.expSingle i + OddMath.SkewPolynomial.expSingle i) 1 +
      OddMath.SkewPolynomial.monomial
        (OddMath.SkewPolynomial.expSingle i + OddMath.SkewPolynomial.expSingle i) 1
      = OddMath.SkewPolynomial.monomial
        (OddMath.SkewPolynomial.expSingle i + OddMath.SkewPolynomial.expSingle i) 2 := by
    show Finsupp.single _ _ + Finsupp.single _ _
      = OddMath.SkewPolynomial.monomial _ _
    rw [← Finsupp.single_add]
    norm_num [OddMath.SkewPolynomial.monomial]
  rw [h2]
  show Finsupp.single _ (2 : ℤ) ≠ 0
  exact Finsupp.single_ne_zero.mpr (by norm_num)

/-- N = 1 must-fail control: the distinct-generator anticommutator law does
NOT apply to the single generator with itself (its double square is nonzero). -/

theorem diagonal_anticomm_ne_zero (i : Fin 1) :
    OddMath.PbwL2.q 1 i * OddMath.PbwL2.q 1 i +
      OddMath.PbwL2.q 1 i * OddMath.PbwL2.q 1 i ≠ 0 := by
  intro h
  exact diagonal_image_ne_zero i (by rw [h, map_zero])

/-- N = 1 must-hold control: the dot generator lives in polynomial degree 2. -/
theorem single_generator_degree_two (j : Fin 1) :
    OddMath.SkewPolynomial.generator j ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 2 :=
  OddMath.Frontier.NilHeckeGradedEnd.generator_mem j

/-- N = 1 must-hold control: the polynomial action hits the generator. -/
theorem single_action_hits_generator (i : Fin 1) :
    OddMath.PbwL3.Phi 1 (OddMath.PbwL2.q 1 i) =
      OddMath.SkewPolynomial.generator i :=
  OddMath.PbwL3.Phi_q 1 i

/-- N = 1 Schubert side: the rank-one symmetric group is trivial, so every
length shift vanishes definitionally downstream. -/
theorem schubert_one_trivial (w : Equiv.Perm (Fin 1)) : w = 1 :=
  Subsingleton.elim w 1

#check OddMath.Frontier.PbwEquivalence.Phi_injective
#check OddMath.Frontier.PbwEquivalence.Phi_bijective
#check OddMath.Frontier.PbwEquivalence.orderedBasis
#check OddMath.Frontier.PbwEquivalence.coefficientEquiv
#check OddMath.Frontier.PbwEquivalence.presentedEquiv
#check OddMath.Frontier.PbwEquivalence.Phi_orderedMonomial
#check OddMath.Frontier.NilHeckeGradedEnd.pdegree
#check OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece
#check OddMath.Frontier.NilHeckeGradedEnd.monomial_mem
#check OddMath.Frontier.NilHeckeGradedEnd.polynomial_mul
#check OddMath.Frontier.NilHeckeGradedEnd.one_mem
#check OddMath.Frontier.NilHeckeGradedEnd.support_degree
#check OddMath.Frontier.NilHeckeGradedEnd.polynomial_negative
#check OddMath.Frontier.NilHeckeGradedEnd.polynomial_odd

end OddMath.Frontier.NilHeckeSmallRankControls

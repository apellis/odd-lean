import OddMath.QuiverHecke.PrependBasis
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates

noncomputable section
open OddMath OddMath.QuiverHecke Categorification.TypeA

namespace PrependBasisExamples
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Repeated colours, nonempty old dots, and a nontrivial old permutation. -/
def sample (i : I) : PrependIdx i [i, i]
    (tgt [i, i, i] (cw (prependCrossingWord 2
      (Equiv.swap 0 1, ((prependPermutationEquiv 2).symm (Equiv.swap 0 2)).2)))) :=
  ⟨(2, [0, 1, 1], Equiv.swap 0 1,
    ((prependPermutationEquiv 2).symm (Equiv.swap 0 2)).2),
    by change ([0, 1, 1] : List ℕ).Pairwise (· ≤ ·); decide,
    by
      intro a ha
      change a < 2
      change a ∈ ([0, 1, 1] : List ℕ) at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      omega,
    rfl⟩

example (i : I) : (sample i).lead.1.1 = [0, 0, 1, 2, 2] := rfl

example (i : I) : PrependIdx.leadEquiv.symm (sample i).lead = sample i :=
  PrependIdx.leadEquiv.symm_apply_apply (sample i)

example (i : I) : Approx D Sc (length 3 (sample i).perm)
    (prependElt D Sc (sample i)) (sample i).lead.nf :=
  prependElt_approx D Sc (sample i)

example (i : I) : prependBasis D Sc (sample i) = prependElt D Sc (sample i) :=
  prependBasis_apply D Sc (sample i)

example (i : I) : (prependBasis D Sc).repr (prependElt D Sc (sample i)) =
    Finsupp.single (sample i) 1 := by
  rw [← prependBasis_apply D Sc]
  exact Module.Basis.repr_self _ _

/-- Empty old word, arbitrary new exponent. -/
def heightZero (i : I) (m : ℕ) : PrependIdx i []
    (tgt [i] (cw (prependCrossingWord 0 ((prependPermutationEquiv 0).symm 1)))) :=
  ⟨(m, [], (prependPermutationEquiv 0).symm 1), by simp, by simp, rfl⟩

example (i : I) (m : ℕ) : (heightZero i m).lead.1.1 = List.replicate m 0 := by
  simp [PrependIdx.lead, PrependIdx.dots, heightZero]

example (i : I) (m : ℕ) : Approx D Sc (length 1 (heightZero i m).perm)
    (prependElt D Sc (heightZero i m)) (heightZero i m).lead.nf :=
  prependElt_approx D Sc (heightZero i m)

example (i : I) (m : ℕ) : PrependIdx.leadEquiv.symm (heightZero i m).lead = heightZero i m :=
  PrependIdx.leadEquiv.symm_apply_apply _

end PrependBasisExamples

#print axioms OddMath.QuiverHecke.PrependIdx.leadEquiv
#print axioms OddMath.QuiverHecke.prependElt_eq_comp
#print axioms OddMath.QuiverHecke.prependElt_approx
#print axioms OddMath.QuiverHecke.prependBasis
#print axioms OddMath.QuiverHecke.prependBasis_apply

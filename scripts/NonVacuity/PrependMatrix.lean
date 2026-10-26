import OddMath.QuiverHecke.CyclotomicAction.PrependMatrix

noncomputable section
open OddMath OddMath.QuiverHecke Categorification.TypeA

namespace PrependMatrixExamples
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Repeated colours with old dots and a nonidentity old permutation. -/
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

example (i : I) :
    prependPBWTerm D Sc i (sample i).1.2.2.2 2
      (FiniteHomMatrix.single (sample i).oldWord ⟨[i, i], rfl⟩
        (NFIdx.nf (D := D) (Sc := Sc) (sample i).old)) =
      FiniteHomMatrix.single (sample i).targetWord (prependWord i ⟨[i, i], rfl⟩)
        (prependElt D Sc (sample i)) := prependPBWTerm_old_nf D Sc (sample i)

/-- Empty old word and arbitrary new exponent, including zero. -/
def heightZero (i : I) (m : ℕ) : PrependIdx i []
    (tgt [i] (cw (prependCrossingWord 0 ((prependPermutationEquiv 0).symm 1)))) :=
  ⟨(m, [], (prependPermutationEquiv 0).symm 1), by simp, by simp, rfl⟩

example (i : I) (m : ℕ) :
    prependPBWTerm D Sc i (heightZero i m).1.2.2.2 m
      (FiniteHomMatrix.single (heightZero i m).oldWord ⟨[], rfl⟩
        (NFIdx.nf (D := D) (Sc := Sc) (heightZero i m).old)) =
      FiniteHomMatrix.single (heightZero i m).targetWord (prependWord i ⟨[], rfl⟩)
        (prependElt D Sc (heightZero i m)) := prependPBWTerm_old_nf D Sc (heightZero i m)

example (i : I) (r : Hn D Sc 2) :
    prependPBWTerm D Sc i (sample i).1.2.2.2 2
      (FiniteHomMatrix.single (sample i).oldWord ⟨[i, i], rfl⟩
        (NFIdx.nf (D := D) (Sc := Sc) (sample i).old) * r) =
      FiniteHomMatrix.single (sample i).targetWord (prependWord i ⟨[i, i], rfl⟩)
        (prependElt D Sc (sample i)) * prependAlgebra D Sc i 2 r := by
  rw [prependPBWTerm_right]
  exact congrArg (fun b => b * prependAlgebra D Sc i 2 r)
    (prependPBWTerm_old_nf D Sc (sample i))

end PrependMatrixExamples

#print axioms OddMath.QuiverHecke.affineFirstDot_pow_mul_single
#print axioms OddMath.QuiverHecke.prependShuffleElement_mul_single
#print axioms OddMath.QuiverHecke.prependPBWTerm_single
#print axioms OddMath.QuiverHecke.prependPBWTerm_old_nf

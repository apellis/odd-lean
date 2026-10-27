import OddMath.QuiverHecke.CyclotomicAction.PrependEquivalence

noncomputable section
open OddMath OddMath.QuiverHecke Categorification Categorification.TypeA CategoryTheory
open scoped Classical
namespace PrependEquivalenceExamples
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Repeated colours, old dots, and a nonidentity old permutation. -/
def oldIndex (i : I) : NFIdx [i, i]
    (tgt [i, i] (cw (canWord 2 (Equiv.swap 0 1)))) :=
  ⟨([0, 1], Equiv.swap 0 1), by change ([0, 1] : List ℕ).Pairwise (· ≤ ·); decide,
    by
      intro a ha
      change a < 2
      change a ∈ ([0, 1] : List ℕ) at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      omega,
    by
      have h := sChain_pl [i, i]
        (([0, 1] : List ℕ).map PG.dot ++ cw (canWord 2 (Equiv.swap 0 1)))
      simp only [tgt_append, tgt_map_dot] at h
      convert h using 1⟩

def oldCoefficient (i : I) : Hn D Sc 2 :=
  FiniteHomMatrix.single ⟨_, by simp⟩ ⟨[i, i], rfl⟩
    (NFIdx.nf (D := D) (Sc := Sc) (oldIndex i))

def moving : PrependShuffle 2 := ((prependPermutationEquiv 2).symm (Equiv.swap 0 2)).2

def coefficients (i : I) : (PrependShuffle 2 × ℕ) →₀ Hn D Sc 2 :=
  Finsupp.single (moving, 3) (oldCoefficient D Sc i) +
    Finsupp.single (moving, 0) 1

example (i : I) :
    (prependCoordinateEquiv D Sc i 2).symm
      (prependCoordinateEquiv D Sc i 2 (coefficients D Sc i)) = coefficients D Sc i :=
  prependCoordinateEquiv_symm_roundtrip D Sc i 2 _

example (i : I) :
    prependCoordinateEquiv D Sc i 2
      ((prependCoordinateEquiv D Sc i 2).symm
        (prependPBWCorner D Sc i moving 3 (oldCoefficient D Sc i))) =
      prependPBWCorner D Sc i moving 3 (oldCoefficient D Sc i) :=
  prependCoordinateEquiv_roundtrip D Sc i 2 _

example (i : I) :
    prependCoordinateEquiv D Sc i 2
      (prependRightCoefficients D Sc (oldCoefficient D Sc i) (coefficients D Sc i)) =
      MulOpposite.op (oldCoefficient D Sc i) •
        prependCoordinateEquiv D Sc i 2 (coefficients D Sc i) :=
  prependCoordinateEquiv_right D Sc i 2 _ _

example (i : I) :
    (prependCoordinateEquiv D Sc i 2).symm
      (MulOpposite.op (oldCoefficient D Sc i) •
        prependPBWCorner D Sc i moving 3 (oldCoefficient D Sc i)) =
      prependRightCoefficients D Sc (oldCoefficient D Sc i)
        ((prependCoordinateEquiv D Sc i 2).symm
          (prependPBWCorner D Sc i moving 3 (oldCoefficient D Sc i))) :=
  prependCoordinateEquiv_symm_right D Sc i 2 _ _

/-- Height zero and exponent zero use the ambient unit, followed by the old coefficient. -/
def emptyShuffle : PrependShuffle 0 := ((prependPermutationEquiv 0).symm 1).2

example (i : I) :
    (prependCoordinateEquiv D Sc i 0).symm
      (prependCoordinateEquiv D Sc i 0 (Finsupp.single (emptyShuffle, 0) 1)) =
      Finsupp.single (emptyShuffle, 0) 1 :=
  prependCoordinateEquiv_symm_roundtrip D Sc i 0 _

example (i : I) :
    prependCoordinateEquiv D Sc i 0
      ((prependCoordinateEquiv D Sc i 0).symm (prependPBWCorner D Sc i emptyShuffle 0 1)) =
      prependPBWCorner D Sc i emptyShuffle 0 1 :=
  prependCoordinateEquiv_roundtrip D Sc i 0 _

example (i : I) :
    prependCoordinateEquiv D Sc i 2 (coefficients D Sc i) =
      (coefficients D Sc i).sum (fun q b => prependPBWCorner D Sc i q.1 q.2 b) :=
  prependCoordinateEquiv_apply D Sc i 2 _
end PrependEquivalenceExamples

#print axioms OddMath.QuiverHecke.prependExpansion_injective
#print axioms OddMath.QuiverHecke.prependExpansion_exists
#print axioms OddMath.QuiverHecke.prependCoordinateEquiv
#print axioms OddMath.QuiverHecke.prependCoordinateEquiv_roundtrip
#print axioms OddMath.QuiverHecke.prependCoordinateEquiv_symm_roundtrip
#print axioms OddMath.QuiverHecke.prependCoordinateEquiv_right
#print axioms OddMath.QuiverHecke.prependCoordinateEquiv_symm_right

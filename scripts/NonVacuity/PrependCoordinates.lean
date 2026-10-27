import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient

noncomputable section
open OddMath OddMath.QuiverHecke Categorification

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

example (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    prependPermutationEquiv n ((prependPermutationEquiv n).symm w) = w :=
  (prependPermutationEquiv n).apply_symm_apply w

example (n : ℕ) (p : Equiv.Perm (Fin n) × PrependShuffle n) :
    Categorification.TypeA.IsReduced (n + 1) (prependCrossingWord n p) :=
  (prependCrossingWord_spec n p).1

example (i : I) (n : ℕ) (u : PrependShuffle n) (m : ℕ) (b r : Hn D Sc n) :
    prependPBWCorner D Sc i u m (b * r) = MulOpposite.op r • prependPBWCorner D Sc i u m b :=
  prependPBWCorner_right D Sc i u m b r

example (i : I) (u : PrependShuffle 0) (m : ℕ) (b : Hn D Sc 0) :
    (prependPBWCorner D Sc i u m b).1 * prependAlgebra D Sc i 0 1 =
      (prependPBWCorner D Sc i u m b).1 :=
  prependPBWTerm_corner D Sc i u m b

example (i : I) (β : Multiset I) (a : I → Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (u : PrependShuffle (n + 1))
    (m : ℕ) (b : Hn D Sc (n + 1))
    (y : (qCoefficient D Sc i β a ha n).toSVec) (c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n c
        (InductionAlong.Ind.tmul (prependPBWCorner D Sc i u m b) y) =
      InductionAlong.Ind.tmul (prependPBWCorner D Sc i u m b)
        ((qCoefficient D Sc i β a ha n).ract c y) :=
  targetRightCoefficient_tmul D Sc i β a ha n c _ y

example (i : I) (β : Multiset I) (a : I → Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n (b * c) =
      (qCoefficient D Sc i β a ha n).ract c (qCoefficientInsert D Sc i β a ha n b) :=
  qCoefficientInsert_mul D Sc i β a ha n b c

#print axioms OddMath.QuiverHecke.prependPermutation_bijective
#print axioms OddMath.QuiverHecke.prependPermutationEquiv
#print axioms OddMath.QuiverHecke.length_prependPermutation
#print axioms OddMath.QuiverHecke.prependCrossingWord_spec
#print axioms OddMath.QuiverHecke.prependShuffleElement
#print axioms OddMath.QuiverHecke.prependPBWTerm_right
#print axioms OddMath.QuiverHecke.prependPBWTerm_corner
#print axioms OddMath.QuiverHecke.prependPBWCorner_right

import OddMath.QuiverHecke.CyclotomicAction.PrependCoefficientCoordinates

noncomputable section
open OddMath OddMath.QuiverHecke Categorification Categorification.TypeA CategoryTheory
open scoped Classical
namespace PrependTensorCoordinatesExamples
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
    (prependTensorEquiv D Sc i 2 (Hn D Sc 2)).symm
      (prependTensorEquiv D Sc i 2 (Hn D Sc 2) (coefficients D Sc i)) =
      coefficients D Sc i := (prependTensorEquiv D Sc i 2 (Hn D Sc 2)).symm_apply_apply _

example (i : I) :
    prependTensorEquiv D Sc i 2 (Hn D Sc 2)
      ((prependTensorEquiv D Sc i 2 (Hn D Sc 2)).symm
        (InductionAlong.Ind.tmul (prependPBWCorner D Sc i moving 3 (oldCoefficient D Sc i))
          (oldCoefficient D Sc i))) =
      InductionAlong.Ind.tmul (prependPBWCorner D Sc i moving 3 (oldCoefficient D Sc i))
        (oldCoefficient D Sc i) := (prependTensorEquiv D Sc i 2 (Hn D Sc 2)).apply_symm_apply _

/-- No positive-height restriction on the general balanced extension. -/
example (i : I) (x : (PrependShuffle 0 × ℕ) →₀ Hn D Sc 0) :
    (prependTensorEquiv D Sc i 0 (Hn D Sc 0)).symm
      (prependTensorEquiv D Sc i 0 (Hn D Sc 0) x) = x :=
  (prependTensorEquiv D Sc i 0 (Hn D Sc 0)).symm_apply_apply _

example (i : I) (z : InductionAlong.Ind (Hn D Sc 0)
    (prependAlgebra D Sc i 0 : Hn D Sc 0 →ₙ+* Hn D Sc 1)) :
    prependTensorEquiv D Sc i 0 (Hn D Sc 0)
      ((prependTensorEquiv D Sc i 0 (Hn D Sc 0)).symm z) = z :=
  (prependTensorEquiv D Sc i 0 (Hn D Sc 0)).apply_symm_apply _

variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)

/-- A nontrivial finite family with the prescribed shifted coefficient carrier. -/
def shiftedFamily (q : PrependShuffle (r+1)) (b c : CyclotomicAlgebra D Sc a r) :=
  Finsupp.single (q, 2) (qCoefficientInsert D Sc i β a ha r b) +
    Finsupp.single (q, 5) (qCoefficientInsert D Sc i β a ha r c)

example (q : PrependShuffle (r+1)) (b c : CyclotomicAlgebra D Sc a r) :
    (qPrependTensorEquiv D Sc i β a ha r).symm
      (qPrependTensorEquiv D Sc i β a ha r (shiftedFamily D Sc i β a ha r q b c)) =
      shiftedFamily D Sc i β a ha r q b c :=
  (qPrependTensorEquiv D Sc i β a ha r).symm_apply_apply _

example (z : InductionAlong.Ind (qCoefficient D Sc i β a ha r).toSVec
    (prependAlgebra D Sc i (r+1) : Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))) :
    qPrependTensorEquiv D Sc i β a ha r
      ((qPrependTensorEquiv D Sc i β a ha r).symm z) = z :=
  (qPrependTensorEquiv D Sc i β a ha r).apply_symm_apply _

example (z : InductionAlong.Corner (prependAlgebra D Sc i (r+1) :
    Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))) (b : CyclotomicAlgebra D Sc a r)
    (q : PrependShuffle (r+1) × ℕ) :
    (qPrependTensorEquiv D Sc i β a ha r).symm
      (InductionAlong.Ind.tmul z (qCoefficientInsert D Sc i β a ha r b)) q =
      qCoefficientInsert D Sc i β a ha r
        (homMatrixTwist D Sc (r+1) (D.parity i * contentSumParity D β)
          ((prependCoordinateEquiv D Sc i (r+1)).symm z q) • b) :=
  qPrependTensorEquiv_symm_insert D Sc i β a ha r z b q

example (c : CyclotomicAlgebra D Sc a r)
    (z : InductionAlong.Ind (qCoefficient D Sc i β a ha r).toSVec
      (prependAlgebra D Sc i (r+1) : Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1)))
    (q : PrependShuffle (r+1) × ℕ) :
    (qPrependTensorEquiv D Sc i β a ha r).symm
      (targetRightCoefficient D Sc i β a ha r c z) q =
      (qCoefficient D Sc i β a ha r).ract c
        ((qPrependTensorEquiv D Sc i β a ha r).symm z q) :=
  qPrependTensorEquiv_symm_right D Sc i β a ha r c z q

example (q : PrependShuffle (r+1) × ℕ) (b c : CyclotomicAlgebra D Sc a r) :
    qPrependTensorEquiv D Sc i β a ha r
      (Finsupp.single q (qCoefficientInsert D Sc i β a ha r (b*c))) =
      targetRightCoefficient D Sc i β a ha r c
        (qPrependTensorEquiv D Sc i β a ha r
          (Finsupp.single q (qCoefficientInsert D Sc i β a ha r b))) :=
  qPrependTensorEquiv_single_mul D Sc i β a ha r q b c
end PrependTensorCoordinatesExamples

#print axioms OddMath.QuiverHecke.prependTensorEquiv
#print axioms OddMath.QuiverHecke.prependTensorForward_apply
#print axioms OddMath.QuiverHecke.prependTensorBackward_tmul
#print axioms OddMath.QuiverHecke.prependTensorBackward_forward
#print axioms OddMath.QuiverHecke.prependTensorForward_backward
#print axioms OddMath.QuiverHecke.qPrependTensorEquiv
#print axioms OddMath.QuiverHecke.qPrependTensorEquiv_symm_insert
#print axioms OddMath.QuiverHecke.qPrependTensorEquiv_symm_right
#print axioms OddMath.QuiverHecke.qPrependTensorEquiv_single_mul

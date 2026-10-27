import OddMath.QuiverHecke.CyclotomicAction.PrependDotCancellation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

noncomputable section
open StringDiagrams OddMath.QuiverHecke Categorification
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace PrependDotCancellationConsumer

def polys (_ : Bool) : _root_.Polynomial ℚ := _root_.Polynomial.X ^ 3

private theorem polys_parity : CyclotomicPolynomialParity datum polys := by
  intro i m hm
  by_cases h : 3 = m
  · subst m; simp [polys]
  · simp [polys, Polynomial.coeff_X_pow, Ne.symm h] at hm

/-- Repeated odd colours with a genuinely odd coefficient shift. -/
example : datum.parity true * contentSumParity datum ({true, true, true} : Multiset Bool) = 1 := by
  decide

def oldDot : CyclotomicAlgebra datum scalars polys 2 :=
  cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)

abbrev coeff := (qCoefficient datum scalars true {true, true, true} polys polys_parity 2).toSVec
abbrev target := InductionAlong.Ind coeff (prependAlgebra datum scalars true 3 :
  Hn datum scalars 3 →ₙ+* Hn datum scalars 4)

def family (j : PrependShuffle 3) : (PrependShuffle 3 × ℕ) →₀ coeff :=
  Finsupp.single (j, 0)
    (qCoefficientInsert datum scalars true {true, true, true} polys polys_parity 2 (1 + oldDot)) +
  Finsupp.single (j, 3)
    (qCoefficientInsert datum scalars true {true, true, true} polys polys_parity 2 (oldDot ^ 2))

/-- Odd exponents, exponent zero and polynomial-valued coefficients survive raising. -/
example (j : PrependShuffle 3) :
    (targetRightDot datum scalars true {true, true, true} polys polys_parity 2 ^ 2)
      (qPrependTensorEquiv datum scalars true {true, true, true} polys polys_parity 2 (family j)) =
    qPrependTensorEquiv datum scalars true {true, true, true} polys polys_parity 2
      (Finsupp.single (j, 2)
        (qCoefficientInsert datum scalars true {true, true, true} polys polys_parity 2 (1 + oldDot)) +
       Finsupp.single (j, 5)
        (qCoefficientInsert datum scalars true {true, true, true} polys polys_parity 2 (oldDot ^ 2))) := by
  rw [targetRightDot_sq_prepend]
  simp only [family, map_add, prependRaiseTwo_single]

/-- The last-dot square and a nonhomogeneous coefficient are both allowed. -/
example : Function.Injective (fun t : target =>
    (targetRightDot datum scalars true {true, true, true} polys polys_parity 2 ^ 2) t -
      targetRightCoefficient datum scalars true {true, true, true} polys polys_parity 2
        (1 + oldDot + oldDot ^ 2) t) :=
  targetRightDot_sq_sub_coefficient_injective datum scalars true {true, true, true}
    polys polys_parity 2 _

example : Function.Injective (fun t : target =>
    (targetRightDot datum scalars true {true, true, true} polys polys_parity 2 ^ 2) t -
      targetRightCoefficient datum scalars true {true, true, true} polys polys_parity 2
        (oldDot ^ 2) t) :=
  targetRightDot_sq_sub_lastDot_sq_injective datum scalars true {true, true, true}
    polys polys_parity 2

/-- Negative squares are also legitimate coefficients; no positivity is imposed. -/
example : Function.Injective (fun t : target =>
    (targetRightDot datum scalars true {true, true, true} polys polys_parity 2 ^ 2) t -
      targetRightCoefficient datum scalars true {true, true, true} polys polys_parity 2
        (-(oldDot ^ 2)) t) :=
  targetRightDot_sq_sub_coefficient_injective datum scalars true {true, true, true}
    polys polys_parity 2 _

/-- The single odd right dot anticommutes, rather than commuting, with the odd coefficient. -/
example :
    (targetRightDotLinear datum scalars true {true, true, true} polys polys_parity 2).comp
      (targetRightCoefficientLinear datum scalars true {true, true, true} polys polys_parity 2 oldDot) =
    -(targetRightCoefficientLinear datum scalars true {true, true, true} polys polys_parity 2 oldDot).comp
      (targetRightDotLinear datum scalars true {true, true, true} polys polys_parity 2) := by
  simpa only [show datum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_smul] using
    targetRightDot_coefficient datum scalars true {true, true, true} polys polys_parity 2 1 oldDot
      (cyclotomicMk_parity datum scalars polys polys_parity 2
        (affineLastDot_parity datum scalars true 2))

/-- Height-zero affine corner and exponent-zero boundary. -/
example (j : PrependShuffle 0) (b : Hn datum scalars 0) :=
  targetDotCorner_twice_prepend datum scalars true j 0 b

/-- The shifted coefficient at r=0 still has affine height one. -/
example := targetRightDot_sq_sub_lastDot_sq_injective datum scalars true {true} polys polys_parity 0

/-- A zero cyclotomic quotient is permitted, not excluded by nontriviality. -/
private theorem one_parity : CyclotomicPolynomialParity datum (fun _ => (1 : _root_.Polynomial ℚ)) := by
  intro i m hm
  by_cases h : m = 0
  · subst m; simp
  · simp [Polynomial.coeff_one, h] at hm

example := targetRightDot_sq_sub_coefficient_injective datum scalars true {true}
  (fun _ => 1) one_parity 0 0

#print axioms prependPBWTerm_mul_sq
#print axioms targetRightDot_sq_prepend
#print axioms qPrependTensorEquiv_symm_sq
#print axioms targetRightDot_sq_eq_coefficient
#print axioms targetRightDot_sq_sub_coefficient_injective
#print axioms targetRightDot_sq_sub_lastDot_sq_injective
end PrependDotCancellationConsumer

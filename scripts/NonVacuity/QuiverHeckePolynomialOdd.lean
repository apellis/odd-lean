import OddMath

/-! The integral odd nilHecke action on the all-odd mixed coefficient module. -/
noncomputable section
namespace OddMath.QuiverHecke.NonVacuityPolynomialOdd
open OddMath.QuiverHecke.Polynomial

example (f g : Polynomial ℤ 2 (fun _ => true)) :
    allOddEquiv 2 (f * g) = allOddEquiv 2 f * allOddEquiv 2 g := map_mul _ _ _

example : Function.Injective (oddNilHeckeAction 0) := oddNilHeckeAction_injective 0

example (f : Polynomial ℤ 2 (fun _ => true)) :
    oddNilHeckeAction 0 (Frontier.NilHeckeAction.dot 0 0) f = X (fun _ => true) 0 * f :=
  oddNilHeckeAction_dot_apply 0 0 f

example : oddNilHeckeAction 0 (Frontier.NilHeckeAction.crossing 0 0)
    (X (fun _ => true) 0) = 1 := by
  apply (allOddEquiv 2).injective
  rw [oddNilHeckeAction_crossing_apply, allOddEquiv_X, map_one]
  simp [Frontier.AllRankDivided.divided_generator]

#print axioms allOddEquiv
#print axioms oddNilHeckeAction_injective

end OddMath.QuiverHecke.NonVacuityPolynomialOdd

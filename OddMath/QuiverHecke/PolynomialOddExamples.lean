/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PolynomialOdd

/-! Consumers of the all-odd specialization used in HW Proposition 4.5. -/
noncomputable section
namespace OddMath.QuiverHecke.PolynomialOddExamples
open OddMath.QuiverHecke.Polynomial

example (n : ℕ) (f g : Polynomial ℤ n (fun _ => true)) :
    allOddEquiv n (f * g) = allOddEquiv n f * allOddEquiv n g := map_mul _ _ _

example (n : ℕ) (i : Fin n) :
    allOddEquiv n (X (fun _ => true) i) = SkewPolynomial.generator i := allOddEquiv_X i

example (n : ℕ) : Function.Injective (oddNilHeckeAction n) := oddNilHeckeAction_injective n

example (n : ℕ) (i : Fin (n + 2)) (f : Polynomial ℤ (n + 2) (fun _ => true)) :
    oddNilHeckeAction n (Frontier.NilHeckeAction.dot n i) f = X (fun _ => true) i * f :=
  oddNilHeckeAction_dot_apply n i f

example (n : ℕ) (i : Fin (n + 1)) (f : Polynomial ℤ (n + 2) (fun _ => true)) :
    allOddEquiv (n + 2) (oddNilHeckeAction n (Frontier.NilHeckeAction.crossing n i) f) =
      Frontier.AllRankDivided.divided i (allOddEquiv (n + 2) f) :=
  oddNilHeckeAction_crossing_apply n i f

/-- A crossing is not zero: it sends its left variable to the unit. -/
example : oddNilHeckeAction 0 (Frontier.NilHeckeAction.crossing 0 0)
    (X (fun _ => true) 0) = 1 := by
  apply (allOddEquiv 2).injective
  rw [oddNilHeckeAction_crossing_apply, allOddEquiv_X, map_one]
  simp [Frontier.AllRankDivided.divided_generator]

#print axioms allOddEquiv
#print axioms oddNilHeckeAction_injective
#print axioms oddNilHeckeAction_dot_apply
#print axioms oddNilHeckeAction_crossing_apply

end OddMath.QuiverHecke.PolynomialOddExamples

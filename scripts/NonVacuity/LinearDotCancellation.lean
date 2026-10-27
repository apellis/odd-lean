import OddMath.QuiverHecke.CyclotomicAction.LinearDotCancellation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

noncomputable section
open StringDiagrams Categorification OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace LinearDotCancellationConsumer

def polys (_ : Bool) : _root_.Polynomial ℚ := _root_.Polynomial.X ^ 3
private theorem polys_parity : CyclotomicPolynomialParity datum polys := by
  intro i m hm
  by_cases h : 3 = m
  · subst m; simp [polys]
  · simp [polys, Polynomial.coeff_X_pow, Ne.symm h] at hm

def colours : Multiset Bool := {true, true, true}

local notation "D" => targetRightDot datum scalars true colours polys polys_parity 2
local notation "R" => targetRightCoefficient datum scalars true colours polys polys_parity 2
local notation "z" => cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)

/-- Repeated odd colour and the odd cubic shift use anticommutation. -/
example (t) : D (R z t) = -(R z (D t)) :=
  targetRightDot_lastDot_odd datum scalars true colours polys polys_parity 2 rfl t

example (t) : D (D t - R z t) - R z (D t - R z t) = (D ^ 2) t + R (z ^ 2) t :=
  targetRightDot_sub_lastDot_odd_square datum scalars true colours
    polys polys_parity 2 rfl t

example : Function.Injective (fun t => D t - R z t) :=
  targetRightDot_sub_lastDot_injective datum scalars true colours polys polys_parity 2

/-- The conclusion applies to the independent content tensor, not just the full target. -/
example : Function.Injective
    (fun t : contentTargetTensor datum scalars true colours polys polys_parity 2 =>
      contentTargetRightDot datum scalars true colours polys polys_parity 2 t -
      contentTargetRightCoefficient datum scalars true colours polys polys_parity 2 z t) :=
  contentTargetRightDot_sub_lastDot_injective datum scalars true colours polys polys_parity 2

/-- The even branch is instantiated at height zero for any even colour. -/
example {I k X : Type} [AddCommGroup X] [CommRing k] [Fintype I]
    (d : OddMath.SKM.Datum I X) (sc : OddMath.SKM.Scalars d k)
    (i : I) (hp : d.parity i = 0) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity d a) (t) :=
  targetRightDot_sub_lastDot_even_product d sc i {i} a ha 0 hp t
example := contentTargetRightDot_sub_lastDot_injective datum scalars false {false} polys polys_parity 0
example := contentTargetRightDot_sub_lastDot_injective datum scalars true {true} polys polys_parity 0

private theorem one_parity : CyclotomicPolynomialParity datum (fun _ => (1 : _root_.Polynomial ℚ)) := by
  intro i m hm
  by_cases h : m = 0
  · subst m; simp
  · simp [Polynomial.coeff_one, h] at hm

/-- The constant-one polynomial permits the zero cyclotomic quotient. -/
example := contentTargetRightDot_sub_lastDot_injective datum scalars true {true}
  (fun _ => 1) one_parity 0

#print axioms targetRightDot_lastDot_even
#print axioms targetRightDot_lastDot_odd
#print axioms targetRightDot_sub_lastDot_odd_square
#print axioms targetRightDot_sub_lastDot_even_product
#print axioms targetRightDot_sub_lastDot_injective
#print axioms contentTargetRightDot_sub_lastDot_injective
end LinearDotCancellationConsumer

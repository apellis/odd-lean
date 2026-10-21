import OddMath

open OddMath.SKM.DividedPowerIdempotents

example : ¬ IsIdempotentElem (rationalPrintedGenerator 0 0) :=
  rationalPrintedGenerator_not_idempotent 0

example : IsIdempotentElem (oppositeProjector 1) := oppositeProjector_idempotent 1

example : oppositeProjector 1 ∈ OddMath.Diagrams.OddNilHecke.parity 1 0 :=
  oppositeProjector_even 1

example : unsignedGenerator 1 0 * unsignedGenerator 1 1 * unsignedGenerator 1 0 =
    unsignedGenerator 1 1 * unsignedGenerator 1 0 * unsignedGenerator 1 1 :=
  unsignedGenerator_braid 0 1 rfl

example : IsIdempotentElem (dividedPower 0) := dividedPower_idempotent 0
example : IsIdempotentElem (dividedPower 1) := dividedPower_idempotent 1
example : IsIdempotentElem (dividedPower 4) := dividedPower_idempotent 4

#print axioms dividedPower_idempotent
#print axioms demazure_longest
#print axioms rationalPrintedGenerator_not_idempotent
#print axioms unsignedProduct_reduced_eq
#print axioms oppositeProjector_idempotent
#print axioms oppositeProjector_degree
#print axioms oppositeProjector_even
#print axioms printed_longest_leftIdeal

import OddMath

/-! Concrete consumers of the signed mixed exchange, HW v2 (4.22). -/
noncomputable section
namespace OddMath.QuiverHecke.NonVacuityExchange
open Polynomial Polynomial.ExchangeExamples

example : exchange (R := ℤ) mixed 0 1 (X mixed 3) =
    -X (exchangeParity mixed 0 1) 3 := distant_odd

example : exchange (R := ℤ) mixed 0 1 (X mixed 2) =
    X (exchangeParity mixed 0 1) 2 := distant_even

example : exchange (R := ℤ) ![false, true] 0 1 (X ![false, true] 0) =
    X (exchangeParity ![false, true] 0 1) 1 := even_odd

example (f : Polynomial ℤ 4 mixed) :
    exchange (exchangeParity mixed 0 1) 0 1 (exchange mixed 0 1 f) = f :=
  exchange_twice mixed 0 1 f

example : characteristicTwo (X mixed 3 ^ 2) ≠ 0 := characteristicTwo_square

#print axioms exchangeAlgEquiv
#print axioms exchange_X_mul
end OddMath.QuiverHecke.NonVacuityExchange

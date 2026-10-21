import OddMath

/-! The Clifford factor restoring KKT's distant crossing sign. -/
noncomputable section
namespace OddMath.QuiverHecke.NonVacuityCliffordExchange
open OddMath.QuiverHecke.CliffordExchange CliffordExchange.Examples

example : Nontrivial (CliffordAlgebra form) := inferInstance

example : (generator 0 - generator 1) * (generator 2 - generator 3) =
    -((generator 2 - generator 3) * (generator 0 - generator 1)) := distant_differences

example : (generator 0 - generator 1) ^ 2 = 2 := difference_square 0 1 (by decide)

example : generator 0 - generator 1 ≠ 0 := difference_ne_zero 0 1 (by decide)

example (p q : Bool) :
    (factor (generator 0) (generator 1) p * 1) *
      (factor (generator 2) (generator 3) q * 1) =
      (if p && q then -1 else 1) *
        ((factor (generator 2) (generator 3) q * 1) *
          (factor (generator 0) (generator 1) p * 1)) := distant_parities p q

#print axioms distant
#print axioms difference_ne_zero
end OddMath.QuiverHecke.NonVacuityCliffordExchange

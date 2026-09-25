import OddMath.Diagrammatics.Even.Basic

/-! Hand-derived endpoint tests for even strand cancellation (TDD fixtures).
Lean index 0 = paper strand 1; `seq below above` applies `below` first.
These mirror an unpublished note exactly. -/
namespace OddMath.Diagrammatics.Even.Tests

open Even

-- F-swap30-map: single swap s₀ on 3 strands sends 0 ↦ 1, 1 ↦ 0, 2 ↦ 2.
example : denote (Expr.swap 1 0) 0 = 1 := by decide
example : denote (Expr.swap 1 0) 1 = 0 := by decide
example : denote (Expr.swap 1 0) 2 = 2 := by decide

-- F-invalid-single (positive form): a single swap is not the identity.
example : denote (Expr.swap 1 (0 : Fin 2)) 0 ≠ denote (Expr.id 3) 0 := by decide

-- F-cancel-30: doubled s₀ fixes every endpoint.
example : denote (Expr.seq (Expr.swap 1 0) (Expr.swap 1 0)) 0 = 0 := by decide
example : denote (Expr.seq (Expr.swap 1 0) (Expr.swap 1 0)) 1 = 1 := by decide
example : denote (Expr.seq (Expr.swap 1 0) (Expr.swap 1 0)) 2 = 2 := by decide

-- F-order-s0s1: chronological s₀ then s₁ sends 0 ↦ 2.
example : denote (Expr.seq (Expr.swap 1 0) (Expr.swap 1 1)) 0 = 2 := by decide

-- F-order-s1s0: reversed order differs (1 ↦ 2, not ↦ 0).
example : denote (Expr.seq (Expr.swap 1 1) (Expr.swap 1 0)) 0 = 1 := by decide

-- F-cancel-40-mid: middle swap twice on 4 strands fixes every endpoint.
example : denote (Expr.seq (Expr.swap 2 1) (Expr.swap 2 1)) 1 = 1 := by decide
example : denote (Expr.seq (Expr.swap 2 1) (Expr.swap 2 1)) 2 = 2 := by decide

-- F-id01 / F-id00: identities fix endpoints.
example : denote (Expr.id 1) 0 = 0 := by decide

end OddMath.Diagrammatics.Even.Tests

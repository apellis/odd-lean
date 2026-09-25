import OddMath.LrTriangular
import Mathlib.Data.Fin.VecNotation

/-! Hand-derived LR triangular fixtures.

Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1,
Thm 3.8 proof (paper lines 508-520): both Schur families satisfy
`s_(lam^T_1) ... s_(lam^T_r) = sum_mu ± s_mu` with shared signs, so both
equal the same expression in the elementary functions.

Values below are hand-derived from the stated row equations BEFORE
checking them against Lean:
- A (n=1): `d=[1]`, `C=[[0]]`, `rhs=[5]`, `x=[5]`; the single tail is `0`.
- B (n=2, Leg B `solve_two` shape): `d=[1,1]`, `C=[[0,1],[0,0]]`,
  `rhs=[8,3]`, `x=[5,3]` (top `1 * x_1 = 3`, lower `x_0 + x_1 = 8`).
- C (n=2, mixed signs): `d=[1,-1]`, `C=[[0,1],[0,0]]`, `rhs=[6,-1]`,
  `x=[5,1]` (lower `x_0 + x_1 = 6`, top `-x_1 = -1`).
- D (n=0): degenerate empty system; any two families coincide.
- E (empty tail): the top row (`i = n - 1`) sums to `0`, directly and via
  the `tailSum_top` lemma.
This file MUST fail to elaborate until `OddMath.LrTriangular` exists.
-/

namespace OddMath.LrTriangular.Tests

open OddMath.LrTriangular

-- A: single-row system; the tail is empty and `1 * x = 5` pins `x = 5`.
example : tailSum (![![0]] : Fin 1 → Fin 1 → Int) (![5] : Fin 1 → Int) 0
    = 0 := by decide
example : RowSystem (![1] : Fin 1 → Int) (![![0]] : Fin 1 → Fin 1 → Int)
    (![5] : Fin 1 → Int) (![5] : Fin 1 → Int) := by unfold RowSystem; decide
example : (![5] : Fin 1 → Int) = ![5] :=
  OddMath.LrTriangular.unique ![1] ![![0]] ![5] ![5] ![5]
    (by decide) (by unfold RowSystem; decide) (by unfold RowSystem; decide)

-- B: two-row all-`+1` chain (Leg B `solve_two` shape).
example : tailSum (![![0, 1], ![0, 0]] : Fin 2 → Fin 2 → Int)
    (![5, 3] : Fin 2 → Int) 0 = 3 := by decide
example : RowSystem (![1, 1] : Fin 2 → Int)
    (![![0, 1], ![0, 0]] : Fin 2 → Fin 2 → Int) (![8, 3] : Fin 2 → Int)
    (![5, 3] : Fin 2 → Int) := by unfold RowSystem; decide
example : (![5, 3] : Fin 2 → Int) = ![5, 3] :=
  OddMath.LrTriangular.unique ![1, 1] ![![0, 1], ![0, 0]] ![8, 3] ![5, 3]
    ![5, 3] (by decide) (by unfold RowSystem; decide) (by unfold RowSystem; decide)

-- C: two-row mixed-sign chain (top `-x_1 = -1`, lower `x_0 + x_1 = 6`).
example : RowSystem (![1, -1] : Fin 2 → Int)
    (![![0, 1], ![0, 0]] : Fin 2 → Fin 2 → Int) (![6, -1] : Fin 2 → Int)
    (![5, 1] : Fin 2 → Int) := by unfold RowSystem; decide
example : (![5, 1] : Fin 2 → Int) = ![5, 1] :=
  OddMath.LrTriangular.unique ![1, -1] ![![0, 1], ![0, 0]] ![6, -1] ![5, 1]
    ![5, 1] (by decide) (by unfold RowSystem; decide) (by unfold RowSystem; decide)

-- D: degenerate empty system; any two families coincide.
example : (fun _ : Fin 0 => (0 : Int)) = fun _ => 0 :=
  OddMath.LrTriangular.unique (fun _ => 1) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

-- E: the top row sums to `0`, directly and via the `tailSum_top` lemma.
example : tailSum (![![0, 1], ![0, 0]] : Fin 2 → Fin 2 → Int)
    (![5, 3] : Fin 2 → Int) 1 = 0 := by decide
example : tailSum (![![0, 1], ![0, 0]] : Fin 2 → Fin 2 → Int)
    (![5, 3] : Fin 2 → Int) 1 = 0 :=
  OddMath.LrTriangular.tailSum_top _ _ _ rfl

end OddMath.LrTriangular.Tests

/-
  LR adapter B12 — S4 unit-lead instantiation: the B9-certified unit leads
  instantiate the B11 diagonal (sorry-free).

  Context: the design specification is the
  shape-spec authority; B9 delivered
  the S4 diagonal-unit justification vocabulary (`IsUnitDiag`, `signOf`,
  `diagSign`, `diagOne`, `diagNegOne` with unit theorems and pointwise
  sign bridges); B11 delivered
  the S4 matrix/vector declaration-type slice (`CoeffMat`, `RhsVec`,
  `coeffZero`, `rhsZero`, `coeffDiag` with projection rules and
  non-collapse). B7 delivered
  the S1 census index everything is stated over; B8 and B10
 are read-only context, deliberately NOT consumed (the
  instantiation is order- and family-independent by design). This file
  realizes exactly ONE further composition step — the unit-lead
  instantiation of the diagonal — as compiled Lean. All other the design specification shapes
  (S3 content, S4 content, S5, S6) and end-to-end checks (C1–C8) are NOT
  realized here.

  Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
  the design specification (S4): shared `diagLead` / `coeffMat` / `rhsVec` with the
  justification `∀ i, diagLead wt i = 1 ∨ diagLead wt i = -1` — the exact
  `hlead` premise shape that `OddMath.LrTriangular.unique` consumes, plus
  the matrix and right-hand side the two `RowSystem` instances share.

  What this module proves (sorry-free, `Init` + B7/B9/B11 imports only):
  the B9 unit leads ARE the leads the B11 diagonal expects. No new lead
  assignment is defined here (no new `diagLead` content — that needs the
  B1/B2 proof work DEFERRED per the design specification); instead every theorem composes one
  B9-certified lead with one B11 diagonal rule:
  - `unitLead_one` / `unitLead_negOne` / `unitLead_sign`: the B9 canonical
    and generic sign diagonals satisfy the `IsUnitDiag` justification
    (re-exported through this namespace by direct application, so the
    instantiation site reads as one composed vocabulary);
  - `coeffUnitOne_self` / `coeffUnitOne_offdiag`: the diagonal matrix of
    the all-ones lead reads `1` on the diagonal and `0` off it
    (`coeffDiag_self` / `coeffDiag_offdiag` instantiated at `diagOne`);
  - `coeffUnitNegOne_self` / `coeffUnitNegOne_offdiag`: the same for the
    all-minus-ones lead (`-1` on the diagonal, `0` off it);
  - `coeffUnitSign_self` / `coeffUnitSign_offdiag`: the same for ANY sign
    assignment diagonal (`signOf (s i)` on the diagonal, `0` off it);
  - `coeffUnitOne_ne_zero`: the unit-lead diagonal matrix is not the zero
    matrix (direct composition of `coeffDiag_one_ne_zero`, definitionally
    — `diagOne wt` unfolds to `fun _ => 1`, so no new argument is needed);
  - `coeffUnitNegOne_ne_zero`: the minus-one diagonal matrix is not the
    zero matrix either (the same `congrFun` argument B11 uses, with the
    `-1 ≠ 0` fact);
  - `coeffUnitOne_eq_sign` / `coeffUnitNegOne_eq_sign`: the canonical
    lead-diagonal matrices coincide pointwise with the constant sign
    instances (B9 pointwise bridges pushed through the B11 diagonal).

  Honest boundary (not hidden): the instantiated leads are the two
  canonical constant diagonals plus arbitrary sign assignments — NOT the
  TRUE content-bearing `diagLead` (which signs the paper's Pieri rules
  actually assign needs B1/B2, DEFERRED per the design specification); the bare
  content-bearing `diagLead`, `coeffMat`, `rhsVec` and the `rowSys_P` /
  `rowSys_S` / `schur_compare` instances are NOT defined here, and the
  Mathlib-only `RowSystem` connection is referenced by shape only, never
  imported — this module is `Init` + B7/B9/B11 imports only by design.
  No S1 declaration (`shapeCensus`, `shapeCount`, soundness/completeness/
  nodup, generators), no S2 declaration (`shapeOrder`, `shapeIndex`), no
  B9 declaration (`signOf`, `IsUnitDiag`, `diagSign`, `diagOne`,
  `diagNegOne`, `idx0_lt`), no B10 declaration (`ShapeFam`, `famPlactic`,
  `famSymm`, `fam_pointwise_ne`, `famIdx_nonempty`, `fam_ne`), and no B11
  declaration (`CoeffMat`, `RhsVec`, `coeffZero`, `rhsZero`, `coeffDiag`,
  projection rules, non-collapse) is restated below — everything is
  IMPORTED and composed, never redefined.

  Non-tautology: no Schur object is defined here; the instantiation is
  pure unit-diagonal composition over the imported S1 census index, and
  the two non-collapse theorems show the instantiated diagonal matrices
  are provably distinct from the zero matrix. Names live in
  `OddMath.LrAdapterB12`.
-/

import OddMath.LrAdapterB7
import OddMath.LrAdapterB9
import OddMath.LrAdapterB11

namespace OddMath.LrAdapterB12

open OddMath.LrAdapterB7
open OddMath.LrAdapterB9
open OddMath.LrAdapterB11

/-- The B9 all-ones lead satisfies the unit justification: instantiation
    of `diagOne_isUnit` through this namespace. -/
theorem unitLead_one (wt : Nat) : IsUnitDiag wt (diagOne wt) :=
  diagOne_isUnit wt

/-- The B9 all-minus-ones lead satisfies the unit justification:
    instantiation of `diagNegOne_isUnit`. -/
theorem unitLead_negOne (wt : Nat) : IsUnitDiag wt (diagNegOne wt) :=
  diagNegOne_isUnit wt

/-- Every B9 sign-assignment diagonal satisfies the unit justification:
    instantiation of `diagSign_isUnit`. Whatever content B1/B2 one day
    deliver as a sign assignment, its diagonal already meets the
    justification. -/
theorem unitLead_sign (wt : Nat) (s : Fin (shapeCount wt) → Bool) :
    IsUnitDiag wt (diagSign wt s) :=
  diagSign_isUnit wt s

/-- Diagonal projection at the all-ones lead: the B11 diagonal matrix of
    `diagOne` reads `1` on the diagonal (`coeffDiag_self` composed with
    the `diagOne` computation rule). -/
theorem coeffUnitOne_self (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagOne wt) i i = 1 := by
  rw [coeffDiag_self wt (diagOne wt) i]
  rfl

/-- Off-diagonal vanishing at the all-ones lead (`coeffDiag_offdiag`
    instantiated at `diagOne`). -/
theorem coeffUnitOne_offdiag (wt : Nat) (i j : Fin (shapeCount wt))
    (h : i ≠ j) :
    coeffDiag wt (diagOne wt) i j = 0 :=
  coeffDiag_offdiag wt (diagOne wt) i j h

/-- Diagonal projection at the all-minus-ones lead: `-1` on the
    diagonal. -/
theorem coeffUnitNegOne_self (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagNegOne wt) i i = -1 := by
  rw [coeffDiag_self wt (diagNegOne wt) i]
  rfl

/-- Off-diagonal vanishing at the all-minus-ones lead. -/
theorem coeffUnitNegOne_offdiag (wt : Nat) (i j : Fin (shapeCount wt))
    (h : i ≠ j) :
    coeffDiag wt (diagNegOne wt) i j = 0 :=
  coeffDiag_offdiag wt (diagNegOne wt) i j h

/-- Diagonal projection for ANY sign-assignment diagonal: the B11
    diagonal matrix of a B9 sign diagonal reads the sign entry on the
    diagonal (`coeffDiag_self` composed with the `diagSign` computation
    rule). -/
theorem coeffUnitSign_self (wt : Nat) (s : Fin (shapeCount wt) → Bool)
    (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagSign wt s) i i = signOf (s i) := by
  rw [coeffDiag_self wt (diagSign wt s) i]
  rfl

/-- Off-diagonal vanishing for any sign-assignment diagonal. -/
theorem coeffUnitSign_offdiag (wt : Nat) (s : Fin (shapeCount wt) → Bool)
    (i j : Fin (shapeCount wt)) (h : i ≠ j) :
    coeffDiag wt (diagSign wt s) i j = 0 :=
  coeffDiag_offdiag wt (diagSign wt s) i j h

/-- Non-collapse at the all-ones lead: its diagonal matrix is not the
    zero matrix. `diagOne wt` unfolds definitionally to `fun _ => 1`,
    so this is exactly B11's `coeffDiag_one_ne_zero` — composition by
    definitional instantiation, no new argument. -/
theorem coeffUnitOne_ne_zero (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagOne wt) ≠ coeffZero wt :=
  coeffDiag_one_ne_zero wt i

/-- Non-collapse at the all-minus-ones lead: its diagonal matrix is not
    the zero matrix either (the B11 `congrFun` argument with `-1 ≠ 0`). -/
theorem coeffUnitNegOne_ne_zero (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (diagNegOne wt) ≠ coeffZero wt := by
  intro heq
  have hc : coeffDiag wt (diagNegOne wt) i i = coeffZero wt i i :=
    congrFun (congrFun heq i) i
  rw [coeffDiag_self, coeffZero_apply] at hc
  have hneg : diagNegOne wt i = -1 := rfl
  rw [hneg] at hc
  exact (by decide : (-1 : Int) ≠ 0) hc

/-- The all-ones lead-diagonal matrix coincides pointwise with the
    constant-true sign instance (the B9 pointwise bridge pushed through
    the B11 diagonal). -/
theorem coeffUnitOne_eq_sign (wt : Nat) (i j : Fin (shapeCount wt)) :
    coeffDiag wt (diagOne wt) i j =
      coeffDiag wt (diagSign wt (fun _ => true)) i j := by
  unfold coeffDiag
  rw [diagOne_eq_sign_apply wt i]

/-- The all-minus-ones lead-diagonal matrix coincides pointwise with the
    constant-false sign instance. -/
theorem coeffUnitNegOne_eq_sign (wt : Nat) (i j : Fin (shapeCount wt)) :
    coeffDiag wt (diagNegOne wt) i j =
      coeffDiag wt (diagSign wt (fun _ => false)) i j := by
  unfold coeffDiag
  rw [diagNegOne_eq_sign_apply wt i]

/- Executable spot-values (compiled execution evidence; outputs appear in
   the isolated build log). Index `0` reuses the B9 census witness
   `idx0_lt` (composition evidence, not a new proof); the off-diagonal
   second index uses `by native_decide` at the same scale B7/B11 already
   evaluate (`shapeCount 4 = 5`); proofs are erased at runtime. -/
#eval ("u1", diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("un", diagNegOne 4 ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("cu11", coeffDiag 4 (diagOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("cu10", coeffDiag 4 (diagOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨1, by native_decide⟩)
#eval ("cun11", coeffDiag 4 (diagNegOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("dz", coeffDiag 4 (diagOne 4) ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩ != coeffZero 4 ⟨0, idx0_lt 4 (by decide)⟩ ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("sg", decide (diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩ = diagSign 4 (fun _ => true) ⟨0, idx0_lt 4 (by decide)⟩))
#eval ("cnt4", shapeCount 4)

/- Axiom audit (outputs appear in the isolated build log; expected: the
   instantiations and projection/bridge compositions stay within
   `[propext]` like their B11 parents — and no unfinished-proof axiom
   anywhere). -/
#print axioms unitLead_one
#print axioms unitLead_negOne
#print axioms unitLead_sign
#print axioms coeffUnitOne_self
#print axioms coeffUnitOne_offdiag
#print axioms coeffUnitNegOne_self
#print axioms coeffUnitNegOne_offdiag
#print axioms coeffUnitSign_self
#print axioms coeffUnitSign_offdiag
#print axioms coeffUnitOne_ne_zero
#print axioms coeffUnitNegOne_ne_zero
#print axioms coeffUnitOne_eq_sign
#print axioms coeffUnitNegOne_eq_sign

end OddMath.LrAdapterB12

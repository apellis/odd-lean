/-
  LR adapter B11 — S4 matrix/vector declaration-type shape over the B7 census
  index (sorry-free).

  Context: the design specification is the
  shape-spec authority; B7 delivered
  the S1 census this module builds on; B8 delivered
  the S2 order/index, B9 the S4
  diagonal-unit justification, and B10 the S3
  family-declaration shape — none of which this module consumes (matrix /
  vector declaration types are order-, sign-, and family-independent by
  design). The B7 census module is IMPORTED here, never redefined: no S1
  declaration (`shapeCensus`, `shapeCount`, soundness/completeness/nodup,
  generators), no S2 declaration (`shapeOrder`, `shapeIndex`), no B9
  declaration (`signOf`, `IsUnitDiag`, `diagSign`, `diagOne`, `diagNegOne`,
  `idx0_lt`), and no B10 declaration (`ShapeFam`, `famPlactic`, `famSymm`,
  `fam_pointwise_ne`, `famIdx_nonempty`, `fam_ne`) is restated below. This
  file realizes exactly ONE further the design specification item — the
  matrix/vector declaration-type half of shape S4 — as compiled Lean. All
  other the design specification shapes (S3 content, S4 content, S5, S6) and end-to-end checks
  (C1–C8) are NOT realized here.

  Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
  the design specification (S4): shared `diagLead` / `coeffMat` / `rhsVec` with the
  justification `∀ i, diagLead wt i = 1 ∨ diagLead wt i = -1` — the exact
  `hlead` premise shape that `OddMath.LrTriangular.unique` consumes, plus
  the matrix and right-hand side the two `RowSystem` instances share.

  Honest deviation from the the design specification declaration sketch: the design specification writes bare
  content-bearing `coeffMat (wt)` / `rhsVec (wt)` entries, whose TRUE
  content (which coefficients the paper's Pieri rules actually assign)
  needs the B1 (Lemma 3.5 + external `[EK11]`/`[EKL11]` imports) and B2
  (psi1-psi2 transfer) proof work that is DEFERRED per the design specification. That content is
  NOT defined here. What IS realized is the declaration-type shape around
  any such content: `CoeffMat` states the census-indexed matrix type,
  `RhsVec` the census-indexed vector type, `coeffZero` / `rhsZero` the
  canonical zero instances, and `coeffDiag` the diagonal matrix of ANY
  lead assignment — so whatever content B1/B2 one day delivers, the type
  shape it must inhabit is already compiled, with machine-checked
  pointwise computation rules (`coeffZero_apply`, `rhsZero_apply`,
  `coeffDiag_self`, `coeffDiag_offdiag`) and a proved non-collapse
  (`coeffDiag_one_ne_zero`: the unit diagonal is not the zero matrix).

  Why this is the next-smallest zero-dependence item after B10's S3: S1
  was realized by B7, S2 by B8, the S4 unit predicate by B9, and the S3
  family-declaration type by B10. Of what remains, S4 content (WHICH
  coefficients `coeffMat` / `rhsVec` carry) needs B1/B2 proof work, and S5
  (`rowSys_P`, `rowSys_S`) plus S6 (`schur_compare`) need genuine P/S
  families (scaffold stubs G2/G3 block them) with Pieri proofs. The
  matrix/vector declaration types need only the census index and core
  `Int` operations — zero dependence on Schur objects, Pieri rules, or
  source adjudications.

  What this module proves (sorry-free, `Init` + B7 import only):
  - `CoeffMat`: the the design specification S4 coefficient-matrix type shape;
  - `RhsVec`: the the design specification S4 right-hand-side vector type shape;
  - `coeffZero` / `rhsZero`: the canonical zero instances;
  - `coeffDiag`: the diagonal matrix of any lead assignment;
  - `coeffZero_apply` / `rhsZero_apply`: computation rules;
  - `coeffDiag_self` / `coeffDiag_offdiag`: diagonal projection rules;
  - `coeffDiag_one_ne_zero`: the unit diagonal is not the zero matrix
    (via `congrFun` at a caller-supplied index, so no `funext` axiom and
    no census-nonemptiness proof is needed here).

  Honest boundary (not hidden): the instances are canonical placeholders
  with NO Pieri content (scaffold stubs G1–G3 block genuine coefficient
  content); the Mathlib-only `RowSystem` connection is referenced by shape
  only, never imported — this module is `Init` + B7 import only by design,
  exactly like B7/B8/B9/B10. The bare content-bearing `diagLead`,
  `coeffMat`, `rhsVec` and the `rowSys_P` / `rowSys_S` / `schur_compare`
  instances are NOT defined here (their content needs the B1/B2 proof work
  DEFERRED per the design specification, and genuine families).

  Non-tautology: no Schur object is defined here; the matrix/vector shape
  is pure index combinatorics over the imported S1 census index, and the
  non-collapse theorem shows the two canonical instances are provably
  distinct. Names live in `OddMath.LrAdapterB11`.
-/

import OddMath.LrAdapterB7

namespace OddMath.LrAdapterB11

open OddMath.LrAdapterB7

/-- the design specification S4 coefficient-matrix type shape: a census-indexed square matrix
    over `Int`. The index `Fin (shapeCount wt)` is the `n` the adapter feeds
    to `OddMath.LrTriangular.unique`; a future `coeffMat` must inhabit this
    type. -/
abbrev CoeffMat (wt : Nat) : Type := Fin (shapeCount wt) → Fin (shapeCount wt) → Int

/-- the design specification S4 right-hand-side vector type shape: a census-indexed vector into
    an ambient type `M`. A future `rhsVec` must inhabit `RhsVec wt M`. -/
abbrev RhsVec (wt : Nat) (M : Type) : Type := Fin (shapeCount wt) → M

/-- The zero coefficient matrix. Canonical placeholder instance (no Pieri
    content); see `coeffDiag_one_ne_zero` for its proved distinction from
    the unit diagonal. -/
def coeffZero (wt : Nat) : CoeffMat wt := fun _ _ => 0

/-- The zero right-hand-side vector over `Int`. Canonical placeholder
    instance (no Lemma 3.5 content). -/
def rhsZero (wt : Nat) : RhsVec wt Int := fun _ => 0

/-- The diagonal matrix of an arbitrary lead assignment `d`: off-diagonal
    entries vanish, diagonal entries read off `d`. Whatever TRUE content
    B1/B2 one day deliver for the shared leads, its diagonal matrix must
    have this shape. -/
def coeffDiag (wt : Nat) (d : Fin (shapeCount wt) → Int) : CoeffMat wt :=
  fun i j => if i = j then d i else 0

/-- Computation rule for the zero matrix. -/
theorem coeffZero_apply (wt : Nat) (i j : Fin (shapeCount wt)) :
    coeffZero wt i j = 0 := by
  rfl

/-- Computation rule for the zero vector. -/
theorem rhsZero_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    rhsZero wt i = 0 := by
  rfl

/-- Diagonal projection: a diagonal matrix reads off its lead assignment
    on the diagonal. -/
theorem coeffDiag_self (wt : Nat) (d : Fin (shapeCount wt) → Int)
    (i : Fin (shapeCount wt)) :
    coeffDiag wt d i i = d i := by
  simp [coeffDiag]

/-- Off-diagonal vanishing: a diagonal matrix is zero away from the
    diagonal. -/
theorem coeffDiag_offdiag (wt : Nat) (d : Fin (shapeCount wt) → Int)
    (i j : Fin (shapeCount wt)) (h : i ≠ j) :
    coeffDiag wt d i j = 0 := by
  simp [coeffDiag, h]

/-- Non-collapse: the unit diagonal is not the zero matrix. The witness
    index is caller-supplied, so no census-nonemptiness proof (and no
    `funext` axiom — `congrFun` only) is needed here. -/
theorem coeffDiag_one_ne_zero (wt : Nat) (i : Fin (shapeCount wt)) :
    coeffDiag wt (fun _ => 1) ≠ coeffZero wt := by
  intro heq
  have hc : coeffDiag wt (fun _ => 1) i i = coeffZero wt i i :=
    congrFun (congrFun heq i) i
  rw [coeffDiag_self, coeffZero_apply] at hc
  exact (by decide : (1 : Int) ≠ 0) hc

/- Executable spot-values (compiled execution evidence; outputs appear in
   the isolated build log). Index-validity proofs are `by native_decide`
   compiled evaluations at the same scale B7 already evaluates
   (`shapeCount 4 = 5`); proofs are erased at runtime. -/
#eval ("cz00", coeffZero 4 ⟨0, by native_decide⟩ ⟨0, by native_decide⟩)
#eval ("rz0", rhsZero 4 ⟨0, by native_decide⟩)
#eval ("dg11", coeffDiag 4 (fun _ => 1) ⟨0, by native_decide⟩ ⟨0, by native_decide⟩)
#eval ("dg10", coeffDiag 4 (fun _ => 1) ⟨0, by native_decide⟩ ⟨1, by native_decide⟩)
#eval ("dz", coeffDiag 4 (fun _ => 1) ⟨0, by native_decide⟩ ⟨0, by native_decide⟩ != coeffZero 4 ⟨0, by native_decide⟩ ⟨0, by native_decide⟩)
#eval ("cnt4", shapeCount 4)

/- Axiom audit (outputs appear in the isolated build log; expected: the
   computation and projection rules are axiom-free, the non-collapse
   within `[propext]` — and no unfinished-proof axiom anywhere). -/
#print axioms coeffZero_apply
#print axioms rhsZero_apply
#print axioms coeffDiag_self
#print axioms coeffDiag_offdiag
#print axioms coeffDiag_one_ne_zero

end OddMath.LrAdapterB11

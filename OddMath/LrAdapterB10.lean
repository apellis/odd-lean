/-
  LR adapter B10 — S3 family-declaration shape over the B7 census index (sorry-free).

  Context: the design specification is the
  shape-spec authority; B7 delivered
  the S1 census this module builds on; B8 delivered
  the S2 order/index and B9 the S4
  diagonal-unit justification — neither of which this module consumes.
  The B7 census module is IMPORTED here, never redefined: no S1 declaration
  (`shapeCensus`, `shapeCount`, soundness/completeness/nodup, generators),
  no S2 declaration (`shapeOrder`, `shapeIndex`), and no B9 declaration
  (`signOf`, `IsUnitDiag`, `diagSign`, `diagOne`, `diagNegOne`, `idx0_lt`)
  is restated below. This file realizes exactly ONE further the design specification
  item — the `family-declaration` shape S3 — as compiled Lean. All other the design specification
  shapes (S4 content, S5, S6) and end-to-end checks (C1–C8) are NOT realized
  here.

  Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
  the design specification (S3): one genuine ambient additive group `M` plus two
  INDEPENDENT families `P S : Fin (shapeCount wt) → M` (plactic image family
  `s^p`, symmetrized family `s^s`), defined in distinct ambient structures
  and never collapsed into one definition.

  What IS realized here (the zero-dependence slice of S3): the family-map
  *type* shape `ShapeFam` over the imported census index, plus two
  independent pattern families over the concrete ambient type `Int`
  (`famPlactic`, `famSymm`, distinct closed expressions) with proved
  pointwise and global independence (`fam_pointwise_ne`, `fam_ne`) and a
  census-nonemptiness witness (`famIdx_nonempty`). Stating these types needs
  no Schur object, no Pieri rule, and no group instance — only the census
  index and core `Int` operations.

  Honest boundary (not hidden): the families are pattern placeholders with
  NO Schur content (scaffold stubs G1–G3 block genuine K/P/S objects); the
  Mathlib `AddCommGroup` instance on `Int` and the Mathlib-only `RowSystem`
  connection are referenced by shape only, never imported — this module is
  `Init` + B7 import only by design, exactly like B7/B8/B9. The bare
  content-bearing `diagLead`, `coeffMat`, `rhsVec` and the `rowSys_P` /
  `rowSys_S` / `schur_compare` instances are NOT defined here (their content
  needs the B1/B2 proof work DEFERRED per the design specification, and genuine families).

  Why this is the next-smallest zero-dependence item after B9's S4-unit:
  S1 was realized by B7, S2 by B8, the S4 unit predicate by B9. Of what
  remains, S4 content (WHICH signs `diagLead` assigns, plus `coeffMat` /
  `rhsVec`) needs B1 (Lemma 3.5 + external `[EK11]`/`[EKL11]` imports) and B2
  (psi1-psi2 transfer) proof work, and S5 (`rowSys_P`, `rowSys_S`) plus S6
  (`schur_compare`) need genuine P/S families (scaffold stubs G2/G3 block
  them) with Pieri proofs. The S3 family-declaration type plus independence
  evidence needs only the census index and `Int` core operations — zero
  dependence on Schur objects, Pieri rules, or source adjudications.

  What this module proves (sorry-free, `Init` + B7 import only):
  - `ShapeFam`: the the design specification S3 family-map type shape;
  - `famPlactic` / `famSymm`: two independent pattern families over `Int`;
  - `famPlactic_apply` / `famSymm_apply`: computation rules;
  - `fam_pointwise_ne`: the families differ at every census index;
  - `famIdx_nonempty`: every weight slice is nonempty (the `0 < wt` case
    reuses the B7 singleton lemma; the zero case is new: the empty
    partition is the weight-0 census member);
  - `fam_ne`: the families differ as functions (via `congrFun` at index
    zero, so no `funext` axiom is needed).

  Non-tautology: the independence theorems show the two families are
  provably distinct — no single definition proves anything by construction,
  and no comparison is asserted. Names live in `OddMath.LrAdapterB10`.
-/

import OddMath.LrAdapterB7

namespace OddMath.LrAdapterB10

open OddMath.LrAdapterB7

/-- the design specification S3 family-map type shape: a census-indexed family into an ambient
    type `M`. The index `Fin (shapeCount wt)` is the `n` the adapter feeds
    to `OddMath.LrTriangular.unique`. -/
abbrev ShapeFam (wt : Nat) (M : Type) : Type := Fin (shapeCount wt) → M

/-- Plactic-pattern family over the concrete ambient type `Int`: the
    index-shifted value at each census position. Pattern placeholder only
    (no Schur content); defined by a closed expression independent of
    `famSymm` below. -/
def famPlactic (wt : Nat) : ShapeFam wt Int := fun i => (i.val : Int) + 1

/-- Symmetrized-pattern family over `Int`: the negated index-shifted value.
    Independent definition (distinct closed expression, never collapsed with
    `famPlactic`); see `fam_ne` for the proved non-collapse. -/
def famSymm (wt : Nat) : ShapeFam wt Int := fun i => -((i.val : Int) + 1)

/-- Computation rule for the plactic-pattern family. -/
theorem famPlactic_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    famPlactic wt i = (i.val : Int) + 1 := by
  rfl

/-- Computation rule for the symmetrized-pattern family. -/
theorem famSymm_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    famSymm wt i = -((i.val : Int) + 1) := by
  rfl

/-- Pointwise independence: the two families differ at every census index
    (a shifted index value is positive, hence never its own negation). -/
theorem fam_pointwise_ne (wt : Nat) (i : Fin (shapeCount wt)) :
    famPlactic wt i ≠ famSymm wt i := by
  intro h
  have h1 : famPlactic wt i = (i.val : Int) + 1 := rfl
  have h2 : famSymm wt i = -((i.val : Int) + 1) := rfl
  rw [h1, h2] at h
  omega

/-- Census-index witness: every weight slice is nonempty. The successor case
    reuses the B7 singleton lemma; the zero case is new (the empty partition
    is the weight-0 member). This generalizes the B9 index witness — which
    required `0 < wt` — with a new zero-case proof; it is scaffolding for
    `fam_ne`, not a restatement of B9's S4 item. -/
theorem famIdx_nonempty (wt : Nat) : 0 < shapeCount wt := by
  cases wt with
  | zero => decide
  | succ n => exact List.length_pos_of_mem (shapeCensus_mem_single (Nat.succ_pos n))

/-- Family independence (S3 non-collapse): the two pattern families are
    provably different functions. Via `congrFun` at index zero, so no
    `funext` axiom is needed. -/
theorem fam_ne (wt : Nat) : famPlactic wt ≠ famSymm wt := by
  intro heq
  exact fam_pointwise_ne wt ⟨0, famIdx_nonempty wt⟩ (congrFun heq _)

/- Executable spot-values (compiled execution evidence; outputs appear in
   the isolated build log). Index-validity proofs reuse `famIdx_nonempty`
   (proofs are erased at runtime), so the only kernel census evaluation is
   the `shapeCount 4` spot — the same scale B7 already evaluates. -/
#eval ("fp0", famPlactic 4 ⟨0, famIdx_nonempty 4⟩)
#eval ("fs0", famSymm 4 ⟨0, famIdx_nonempty 4⟩)
#eval ("fp0b", famPlactic 0 ⟨0, famIdx_nonempty 0⟩)
#eval ("fs0b", famSymm 0 ⟨0, famIdx_nonempty 0⟩)
#eval ("fd", famPlactic 4 ⟨0, famIdx_nonempty 4⟩ != famSymm 4 ⟨0, famIdx_nonempty 4⟩)
#eval ("cnt4", shapeCount 4)

/- Axiom audit (outputs appear in the isolated build log; expected: the two
   computation rules are axiom-free, the rest within the B7 census axiom
   set — and no unfinished-proof axiom anywhere). -/
#print axioms famPlactic_apply
#print axioms famSymm_apply
#print axioms fam_pointwise_ne
#print axioms famIdx_nonempty
#print axioms fam_ne

end OddMath.LrAdapterB10

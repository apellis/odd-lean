/-
  LR adapter B9 — S4 diagonal-unit shape over the B7 census index (sorry-free).

  Context: the design specification is the
  shape-spec authority; B7 delivered
  the S1 census this module builds on; B8 delivered
  the S2 order/index, which this module does NOT consume. The B7 census
  module is IMPORTED here, never redefined: no S1 declaration
  (`shapeCensus`, `shapeCount`, soundness/completeness/nodup, generators)
  and no S2 declaration (`shapeOrder`, `shapeIndex`) is restated below.
  This file realizes exactly ONE further the design specification item — the
  `diagonal-unit` justification half of shape S4 — as compiled Lean. All
  other the design specification shapes (S3, S4 content, S5, S6) and end-to-end checks (C1–C8)
  are NOT realized here.

  Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
  the design specification (S4): shared `diagLead`/`coeffMat`/`rhsVec` with the
  justification `∀ i, diagLead wt i = 1 ∨ diagLead wt i = -1` — the exact
  `hlead` premise shape that `OddMath.LrTriangular.unique` consumes.

  Honest deviation from the the design specification declaration sketch: the design specification writes a bare
  content-bearing `diagLead (wt) : Fin (shapeCount wt) → Int`, whose TRUE
  content (which signs the paper's e-right Pieri rule actually assigns)
  needs the B1 (Lemma 3.5) and B2 (psi1-psi2 transfer) proof work that is
  DEFERRED per the design specification. That content is NOT defined here. What IS realized is
  the unit-justification shape around every sign diagonal: `IsUnitDiag`
  states the `±1` predicate, `diagSign` builds a diagonal from ANY sign
  assignment, and the unit theorems prove every such diagonal satisfies
  the predicate — so whatever content B1/B2 one day delivers, the
  justification it must meet is already compiled. The canonical `diagOne`
  / `diagNegOne` diagonals are the two constant instances, with pointwise
  bridge lemmas (stated pointwise, not via `funext`, so the module stays
  axiom-free beyond the B7 import).

  Why this is the next-smallest zero-dependence item after B8's S2: S3
  needs a genuine ambient `AddCommGroup` (scaffold G0 `String` blocks it;
  out of reach for an `Init`-only module), S4 content (which signs,
  `coeffMat`/`rhsVec`) needs B1/B2 proof work, and S5/S6 need genuine
  P/S families (scaffold G2/G3 block them). The diagonal-unit predicate
  needs only `Int` sign combinatorics over the imported census index
  type `Fin (shapeCount wt)` — zero dependence on Schur objects, Pieri
  rules, or source adjudications.

  What this module proves (sorry-free, `Init` + B7 import only):
  - `signOf`: the `±1` entry of one sign bit;
  - `signOf_unit`: every sign bit yields `±1`;
  - `signOf_ne_zero`: no sign bit yields `0`;
  - `IsUnitDiag`: the the design specification S4 / `unique`-hlead justification predicate;
  - `diagSign`: the diagonal of any sign assignment;
  - `diagSign_isUnit`: every sign diagonal is unit;
  - `diagOne` / `diagNegOne`: the canonical constant diagonals;
  - `diagOne_isUnit` / `diagNegOne_isUnit`: they are unit;
  - `diagOne_eq_sign_apply` / `diagNegOne_eq_sign_apply`: pointwise
    bridges exhibiting the canonical diagonals as sign instances.

  Non-tautology: no Schur object is defined here; the diagonal-unit
  shape is pure sign combinatorics over the imported S1 census index.
  Names live in `OddMath.LrAdapterB9`.
-/

import OddMath.LrAdapterB7

namespace OddMath.LrAdapterB9

open OddMath.LrAdapterB7

/-- The `±1` diagonal entry of one sign bit. -/
def signOf : Bool → Int
  | true => 1
  | false => -1

/-- Every sign bit yields `±1`. -/
theorem signOf_unit : ∀ (b : Bool), signOf b = 1 ∨ signOf b = -1 := by
  intro b
  cases b <;> simp [signOf]

/-- No sign bit yields `0` (a unit entry is cancellable, never zero). -/
theorem signOf_ne_zero : ∀ (b : Bool), signOf b ≠ 0 := by
  intro b hb
  cases b <;> simp [signOf] at hb

/-- the design specification S4 justification shape (also the `OddMath.LrTriangular.unique`
    `hlead` premise shape): every diagonal entry is `±1`. Stated over the
    imported census index `Fin (shapeCount wt)` — the `n` the adapter
    feeds to `unique`. (`RowSystem` itself needs Mathlib's `AddCommGroup`
    and is therefore referenced by shape only, never imported.) -/
def IsUnitDiag (wt : Nat) (d : Fin (shapeCount wt) → Int) : Prop :=
  ∀ i, d i = 1 ∨ d i = -1

/-- The diagonal of ANY sign assignment over the census index. -/
def diagSign (wt : Nat) (s : Fin (shapeCount wt) → Bool) :
    Fin (shapeCount wt) → Int :=
  fun i => signOf (s i)

/-- Every sign diagonal is unit: whatever content B1/B2 one day assign,
    the justification they must meet already holds. -/
theorem diagSign_isUnit (wt : Nat) (s : Fin (shapeCount wt) → Bool) :
    IsUnitDiag wt (diagSign wt s) := by
  intro i
  show signOf (s i) = 1 ∨ signOf (s i) = -1
  exact signOf_unit (s i)

/-- The canonical all-ones diagonal. -/
def diagOne (wt : Nat) : Fin (shapeCount wt) → Int := fun _ => 1

/-- The all-ones diagonal is unit. -/
theorem diagOne_isUnit (wt : Nat) : IsUnitDiag wt (diagOne wt) := by
  intro i
  exact Or.inl rfl

/-- Pointwise bridge: the all-ones diagonal is the constant-true sign
    instance (stated pointwise so no `funext` axiom is needed). -/
theorem diagOne_eq_sign_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    diagOne wt i = diagSign wt (fun _ => true) i := by
  rfl

/-- The canonical all-minus-ones diagonal. -/
def diagNegOne (wt : Nat) : Fin (shapeCount wt) → Int := fun _ => -1

/-- The all-minus-ones diagonal is unit. -/
theorem diagNegOne_isUnit (wt : Nat) : IsUnitDiag wt (diagNegOne wt) := by
  intro i
  exact Or.inr rfl

/-- Pointwise bridge: the all-minus-ones diagonal is the constant-false
    sign instance (pointwise, no `funext`). -/
theorem diagNegOne_eq_sign_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    diagNegOne wt i = diagSign wt (fun _ => false) i := by
  rfl

/-- Census-index witness: the singleton partition `[wt]` is always a census
    member (B7 `shapeCensus_mem_single`), so index `0` is always valid.
    This reuses the S1 nonempty-slice lemma — no kernel census computation
    is needed at the use site. -/
theorem idx0_lt (wt : Nat) (hwt : 0 < wt) : 0 < shapeCount wt :=
  List.length_pos_of_mem (shapeCensus_mem_single hwt)

/- Executable spot-values (compiled execution evidence; outputs appear in
   the isolated build log). The `Fin` witnesses reuse `idx0_lt`, so the
   only `decide` goals are the trivial `0 < wt` facts — no deep kernel
   census evaluation at the use site. -/
#eval ("sgT", signOf true)
#eval ("sgF", signOf false)
#eval ("d1", diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("ds", diagSign 2 (fun _ => false) ⟨0, idx0_lt 2 (by decide)⟩)
#eval ("do", decide (diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩ = diagSign 4 (fun _ => true) ⟨0, idx0_lt 4 (by decide)⟩))
#eval ("cnt4", shapeCount 4)

/- Axiom audit (outputs appear in the isolated build log; expected: no
   axioms at all — the proofs below are `cases`/`rfl`, and the bridges
   are deliberately pointwise to avoid `funext`). -/
#print axioms signOf_unit
#print axioms signOf_ne_zero
#print axioms diagSign_isUnit
#print axioms diagOne_isUnit
#print axioms diagNegOne_isUnit
#print axioms diagOne_eq_sign_apply
#print axioms diagNegOne_eq_sign_apply
#print axioms idx0_lt

end OddMath.LrAdapterB9

import OddMath.LrShapeCensus

/-!
# Families indexed by the census

`ShapeFam wt M` is the type `Fin (shapeCount wt) → M` of families indexed by the partitions
of `wt` (`OddMath.LrShapeCensus`). The module gives two explicit `Int`-valued families,
`famPlactic i = i + 1` and `famSymm i = -(i + 1)`; they carry no Schur-function content.

Main results (Lean core only, besides `OddMath.LrShapeCensus`):
- `famPlactic_apply` / `famSymm_apply`: computation rules.
- `fam_pointwise_ne`: the two families differ at every index.
- `famIdx_nonempty`: the census of every weight is nonempty (the empty partition is the
  partition of `0`).
- `fam_ne`: the two families differ as functions.
-/

namespace OddMath.LrShapeFamily

open OddMath.LrShapeCensus

/-- A family indexed by the partitions of `wt`, with values in `M`. -/
abbrev ShapeFam (wt : Nat) (M : Type) : Type := Fin (shapeCount wt) → M

/-- The family `i ↦ i + 1` over `Int` (no Schur-function content). -/
def famPlactic (wt : Nat) : ShapeFam wt Int := fun i => (i.val : Int) + 1

/-- The family `i ↦ -(i + 1)` over `Int` (no Schur-function content). -/
def famSymm (wt : Nat) : ShapeFam wt Int := fun i => -((i.val : Int) + 1)

/-- Computation rule for `famPlactic`. -/
theorem famPlactic_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    famPlactic wt i = (i.val : Int) + 1 := by
  rfl

/-- Computation rule for `famSymm`. -/
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

/-- The census of every weight is nonempty: for `0 < wt` it contains `[wt]`
    (`shapeCensus_mem_single`), and the empty partition is the partition of `0`. -/
theorem famIdx_nonempty (wt : Nat) : 0 < shapeCount wt := by
  cases wt with
  | zero => decide
  | succ n => exact List.length_pos_of_mem (shapeCensus_mem_single (Nat.succ_pos n))

/-- `famPlactic` and `famSymm` are different functions (`congrFun` at index zero). -/
theorem fam_ne (wt : Nat) : famPlactic wt ≠ famSymm wt := by
  intro heq
  exact fam_pointwise_ne wt ⟨0, famIdx_nonempty wt⟩ (congrFun heq _)

/- Evaluated values. Index-validity proofs use `famIdx_nonempty`. -/
#eval ("fp0", famPlactic 4 ⟨0, famIdx_nonempty 4⟩)
#eval ("fs0", famSymm 4 ⟨0, famIdx_nonempty 4⟩)
#eval ("fp0b", famPlactic 0 ⟨0, famIdx_nonempty 0⟩)
#eval ("fs0b", famSymm 0 ⟨0, famIdx_nonempty 0⟩)
#eval ("fd", famPlactic 4 ⟨0, famIdx_nonempty 4⟩ != famSymm 4 ⟨0, famIdx_nonempty 4⟩)
#eval ("cnt4", shapeCount 4)

/- Axiom checks. -/
#print axioms famPlactic_apply
#print axioms famSymm_apply
#print axioms fam_pointwise_ne
#print axioms famIdx_nonempty
#print axioms fam_ne

end OddMath.LrShapeFamily

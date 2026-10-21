import OddMath.LrShapeCensus

/-!
# Sign diagonals over the census index

A unitriangular system (`OddMath.LrTriangular.RowSystem`) has leading coefficients `±1`.
`IsUnitDiag wt d` states this for a diagonal `d : Fin (shapeCount wt) → Int` indexed by the
partitions of `wt` (`OddMath.LrShapeCensus`), and `diagSign` is the diagonal of a sign
assignment `Fin (shapeCount wt) → Bool`. Which signs occur for odd Schur functions is not
determined here.

Main results (Lean core only, besides `OddMath.LrShapeCensus`):
- `signOf`: `true ↦ 1`, `false ↦ -1`; `signOf_unit`, `signOf_ne_zero`.
- `IsUnitDiag`: every diagonal entry is `1` or `-1`.
- `diagSign` / `diagSign_isUnit`: the diagonal of a sign assignment is a unit diagonal.
- `diagOne` / `diagNegOne`: the constant diagonals, with `diagOne_isUnit`,
  `diagNegOne_isUnit` and the pointwise identifications `diagOne_eq_sign_apply`,
  `diagNegOne_eq_sign_apply`.
- `idx0_lt`: the census of a positive weight is nonempty.
-/

namespace OddMath.LrSignDiagonal

open OddMath.LrShapeCensus

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

/-- Unit diagonal: every diagonal entry is `±1`, as in the `hlead` hypothesis of
    `OddMath.LrTriangular.unique`, over the census index `Fin (shapeCount wt)`. -/
def IsUnitDiag (wt : Nat) (d : Fin (shapeCount wt) → Int) : Prop :=
  ∀ i, d i = 1 ∨ d i = -1

/-- The diagonal of a sign assignment over the census index. -/
def diagSign (wt : Nat) (s : Fin (shapeCount wt) → Bool) :
    Fin (shapeCount wt) → Int :=
  fun i => signOf (s i)

/-- Every sign diagonal is a unit diagonal. -/
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

/-- The all-ones diagonal agrees pointwise with the diagonal of the constant-`true`
    sign assignment. -/
theorem diagOne_eq_sign_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    diagOne wt i = diagSign wt (fun _ => true) i := by
  rfl

/-- The canonical all-minus-ones diagonal. -/
def diagNegOne (wt : Nat) : Fin (shapeCount wt) → Int := fun _ => -1

/-- The all-minus-ones diagonal is unit. -/
theorem diagNegOne_isUnit (wt : Nat) : IsUnitDiag wt (diagNegOne wt) := by
  intro i
  exact Or.inr rfl

/-- The all-minus-ones diagonal agrees pointwise with the diagonal of the
    constant-`false` sign assignment. -/
theorem diagNegOne_eq_sign_apply (wt : Nat) (i : Fin (shapeCount wt)) :
    diagNegOne wt i = diagSign wt (fun _ => false) i := by
  rfl

/-- For `0 < wt` the singleton partition `[wt]` is a census member
    (`shapeCensus_mem_single`), so index `0` is valid. -/
theorem idx0_lt (wt : Nat) (hwt : 0 < wt) : 0 < shapeCount wt :=
  List.length_pos_of_mem (shapeCensus_mem_single hwt)

/- Evaluated values. The `Fin` witnesses use `idx0_lt`, so the only `decide` goals are
   `0 < wt`. -/
#eval ("sgT", signOf true)
#eval ("sgF", signOf false)
#eval ("d1", diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩)
#eval ("ds", diagSign 2 (fun _ => false) ⟨0, idx0_lt 2 (by decide)⟩)
#eval ("do", decide (diagOne 4 ⟨0, idx0_lt 4 (by decide)⟩ = diagSign 4 (fun _ => true) ⟨0, idx0_lt 4 (by decide)⟩))
#eval ("cnt4", shapeCount 4)

/- Axiom checks. -/
#print axioms signOf_unit
#print axioms signOf_ne_zero
#print axioms diagSign_isUnit
#print axioms diagOne_isUnit
#print axioms diagNegOne_isUnit
#print axioms diagOne_eq_sign_apply
#print axioms diagNegOne_eq_sign_apply
#print axioms idx0_lt

end OddMath.LrSignDiagonal

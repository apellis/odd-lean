import OddMath.Frontier.EKClassicalPlactic

/-!
# Audit for EK Theorem 4.1 (classical plactic monoid)

Pins the exact statements of the headline results by type ascription and prints the axioms
of every owned declaration (expected: at most `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace OddMath.Frontier.EKClassicalPlacticAudit

open OddMath.Frontier OddMath.Frontier.EKClassicalPlactic OddMath.Frontier.TableauSign

/-- Printed relations, verbatim shape: (K′) `yzx = yxz` if `x < y ≤ z`; (K″) `xzy = zxy` if `x ≤ y < z`. -/
example (w w' : List ℕ) : KStep w w' ↔ ∃ (u v : List ℕ) (x y z : ℕ),
    (x < y ∧ y ≤ z ∧ w = u ++ [y, z, x] ++ v ∧ w' = u ++ [y, x, z] ++ v) ∨
    (x ≤ y ∧ y < z ∧ w = u ++ [x, z, y] ++ v ∧ w' = u ++ [z, x, y] ++ v) := Iff.rfl

example (w w' : List ℕ) : KnuthEquiv w w' ↔ Relation.EqvGen KStep w w' := Iff.rfl

/-- EK Theorem 4.1, exact statement. -/
example : ∀ w : List ℕ, (∀ a ∈ w, 0 < a) →
    ∃! S : Σ μ : YoungDiagram, PositiveTableau μ, KnuthEquiv w (TableauRowWord.rowWord S.2) :=
  theorem_4_1

/-- "namely its insertion tableau" (existing `TableauWordInsertion.run` from empty). -/
example (n : ℕ) (w : List (Fin n)) :
    KnuthEquiv (w.map lab) (TableauRowWord.rowWord (insertionTableau n w).2) ∧
    ∀ S : Σ μ : YoungDiagram, PositiveTableau μ,
      KnuthEquiv (w.map lab) (TableauRowWord.rowWord S.2) → S = insertionTableau n w :=
  theorem_4_1_insertion n w

example (n : ℕ) (w : List (Fin n)) : insertionTableau n w =
    ⟨(TableauWordInsertion.run n (emptyState n) w).1.1,
      (TableauWordInsertion.run n (emptyState n) w).1.2.1⟩ := rfl

/-- Uniqueness in tableau form. -/
example {μ μ' : YoungDiagram} (T : PositiveTableau μ) (T' : PositiveTableau μ')
    (hk : KnuthEquiv (TableauRowWord.rowWord T) (TableauRowWord.rowWord T')) :
    (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩ := tableau_eq_of_knuth T T' hk

/-- Plactic monoid presented by exactly the printed relations; tableau basis of `ℤPl`. -/
example : knuthCon = conGen (fun a b : FreeMonoid ℕ =>
    KStep (FreeMonoid.toList a) (FreeMonoid.toList b)) := knuthCon_eq_conGen

example : Function.Bijective tabToPl := tabToPl_bijective

noncomputable example : Basis (Σ μ : YoungDiagram, PositiveTableau μ) ℤ (MonoidAlgebra ℤ Pl) :=
  tableauBasis

example (S : Σ μ : YoungDiagram, PositiveTableau μ) :
    tableauBasis S = MonoidAlgebra.of ℤ Pl (tabToPl S) := tableauBasis_apply S

/-- Source control, EK Example 4.2 (p.32): `w = 53422331112` is the row word (left to right,
bottom to top) of the tableau with rows `1112 / 2233 / 34 / 5`, and insertion of `w` returns
exactly that tableau. -/
example : readR [[1, 1, 1, 2], [2, 2, 3, 3], [3, 4], [5]] = [5, 3, 4, 2, 2, 3, 3, 1, 1, 1, 2] := rfl

example : P [5, 3, 4, 2, 2, 3, 3, 1, 1, 1, 2] = [[1, 1, 1, 2], [2, 2, 3, 3], [3, 4], [5]] := by
  decide

example : Valid [[1, 1, 1, 2], [2, 2, 3, 3], [3, 4], [5]] ∧
    P (readR [[1, 1, 1, 2], [2, 2, 3, 3], [3, 4], [5]]) = [[1, 1, 1, 2], [2, 2, 3, 3], [3, 4], [5]] := by
  refine ⟨?_, P_readR _ ?_⟩ <;>
    simp [Valid, Dom, List.Sorted, List.pairwise_cons]

example (S : Σ μ : YoungDiagram, PositiveTableau μ) :
    tabToPl S = 1 ↔ TableauRowWord.rowWord S.2 = [] := tabToPl_eq_one_iff S

/-- The printed non-unital `Pl` ("monoid (without unit)"): the elements `≠ 1`, a
subsemigroup; nonempty SSYT biject with it and give a `ℤ`-basis of its monoid algebra. -/
example (x : Pl) : x ∈ PlNonunital ↔ x ≠ 1 := Iff.rfl

example (x y : Pl) (hx : x ≠ 1) (hy : y ≠ 1) : x * y ≠ 1 :=
  PlNonunital.mul_mem (show x ∈ PlNonunital from hx) (show y ∈ PlNonunital from hy)

noncomputable example :
    {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []} ≃
      PlNonunital := tabEquivPlNonunital

example (S : {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []}) :
    ((tabEquivPlNonunital S : PlNonunital) : Pl) = tabToPl S.1 := tabEquivPlNonunital_apply S

noncomputable example :
    Basis {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []} ℤ
      (MonoidAlgebra ℤ PlNonunital) := tableauBasisNonunital

example (S : {S : Σ μ : YoungDiagram, PositiveTableau μ // TableauRowWord.rowWord S.2 ≠ []}) :
    tableauBasisNonunital S = Finsupp.single (tabEquivPlNonunital S) (1 : ℤ) :=
  tableauBasisNonunital_apply S

/-- Non-vacuity of the non-unital index set: the one-box tableau `[1]` has row word `[1]`. -/
example : ∃ S : Σ μ : YoungDiagram, PositiveTableau μ, TableauRowWord.rowWord S.2 = [1] := by
  obtain ⟨S, hS, -⟩ := theorem_4_1 [1] (by simp)
  have hp := perm_of_knuth hS
  exact ⟨S, (List.perm_singleton.mp hp.symm)⟩

#print axioms EKClassicalPlactic.mk_eq_one_iff
#print axioms EKClassicalPlactic.PlNonunital
#print axioms EKClassicalPlactic.ZPlNonunital
#print axioms EKClassicalPlactic.tabEquivPlNonunital
#print axioms EKClassicalPlactic.tabEquivPlNonunital_apply
#print axioms EKClassicalPlactic.tableauBasisNonunital
#print axioms EKClassicalPlactic.tableauBasisNonunital_apply
#print axioms EKClassicalPlactic.knuth_nil_iff
#print axioms EKClassicalPlactic.tabToPl_eq_one_iff
#print axioms EKClassicalPlactic.bump1
#print axioms EKClassicalPlactic.ins
#print axioms EKClassicalPlactic.insW
#print axioms EKClassicalPlactic.P
#print axioms EKClassicalPlactic.readR
#print axioms EKClassicalPlactic.KStep
#print axioms EKClassicalPlactic.KnuthEquiv
#print axioms EKClassicalPlactic.local3
#print axioms EKClassicalPlactic.moves
#print axioms EKClassicalPlactic.wordsOf
#print axioms EKClassicalPlactic.wordsUpTo
#print axioms EKClassicalPlactic.colStrictB
#print axioms EKClassicalPlactic.sortedB
#print axioms EKClassicalPlactic.validB
#print axioms EKClassicalPlactic.closeStep
#print axioms EKClassicalPlactic.closure
#print axioms EKClassicalPlactic.controlWords
#print axioms EKClassicalPlactic.wrongLocal3
#print axioms EKClassicalPlactic.RowsSorted
#print axioms EKClassicalPlactic.rowIns
#print axioms EKClassicalPlactic.E3
#print axioms EKClassicalPlactic.Dom
#print axioms EKClassicalPlactic.Valid
#print axioms EKClassicalPlactic.lab
#print axioms EKClassicalPlactic.PosWord
#print axioms EKClassicalPlactic.Pl
#print axioms EKClassicalPlactic.ZPl
#print axioms EKClassicalPlactic.bump1_nil
#print axioms EKClassicalPlactic.bump1_cons_lt
#print axioms EKClassicalPlactic.bump1_cons_le
#print axioms EKClassicalPlactic.bump1_append_le
#print axioms EKClassicalPlactic.bump1_le_all
#print axioms EKClassicalPlactic.bump1_spec
#print axioms EKClassicalPlactic.sorted_split
#print axioms EKClassicalPlactic.bump1_sorted
#print axioms EKClassicalPlactic.ins_sorted
#print axioms EKClassicalPlactic.insW_sorted
#print axioms EKClassicalPlactic.insW_append
#print axioms EKClassicalPlactic.P_sorted
#print axioms EKClassicalPlactic.insW_cons_rows
#print axioms EKClassicalPlactic.rowIns_length
#print axioms EKClassicalPlactic.E3_symm
#print axioms EKClassicalPlactic.E3_length
#print axioms EKClassicalPlactic.sorted_split4
#print axioms EKClassicalPlactic.row_K2
#print axioms EKClassicalPlactic.row_K1
#print axioms EKClassicalPlactic.row_E3
#print axioms EKClassicalPlactic.rowIns_nil_length
#print axioms EKClassicalPlactic.insW_nil_eq
#print axioms EKClassicalPlactic.insW_E3
#print axioms EKClassicalPlactic.E3_of_KStep_core
#print axioms EKClassicalPlactic.insW_KStep
#print axioms EKClassicalPlactic.P_eq_of_knuth
#print axioms EKClassicalPlactic.KStep_context
#print axioms EKClassicalPlactic.knuth_context
#print axioms EKClassicalPlactic.knuth_refl
#print axioms EKClassicalPlactic.knuth_symm
#print axioms EKClassicalPlactic.knuth_trans
#print axioms EKClassicalPlactic.knuth_K1
#print axioms EKClassicalPlactic.knuth_K2
#print axioms EKClassicalPlactic.knuth_move_right_part
#print axioms EKClassicalPlactic.knuth_move_left_part
#print axioms EKClassicalPlactic.knuth_row_bump
#print axioms EKClassicalPlactic.knuth_ins
#print axioms EKClassicalPlactic.knuth_readR_insW
#print axioms EKClassicalPlactic.knuth_readR_P
#print axioms EKClassicalPlactic.dom_nil
#print axioms EKClassicalPlactic.rowIns_dom
#print axioms EKClassicalPlactic.insW_row
#print axioms EKClassicalPlactic.P_readR
#print axioms EKClassicalPlactic.valid_eq_of_knuth
#print axioms EKClassicalPlactic.perm_of_knuth
#print axioms EKClassicalPlactic.lab_injective
#print axioms EKClassicalPlactic.lab_le
#print axioms EKClassicalPlactic.lab_lt
#print axioms EKClassicalPlactic.runRows_map
#print axioms EKClassicalPlactic.foldl_runRows_map
#print axioms EKClassicalPlactic.run_rows
#print axioms EKClassicalPlactic.emptyTableau
#print axioms EKClassicalPlactic.emptyTableau_inAlphabet
#print axioms EKClassicalPlactic.emptyState
#print axioms EKClassicalPlactic.rows_empty
#print axioms EKClassicalPlactic.insertionTableau
#print axioms EKClassicalPlactic.insertionTableau_inAlphabet
#print axioms EKClassicalPlactic.insertionTableau_rows
#print axioms EKClassicalPlactic.rowWord_eq_readR
#print axioms EKClassicalPlactic.dom_of_columnBelow
#print axioms EKClassicalPlactic.valid_of_rows
#print axioms EKClassicalPlactic.valid_rows
#print axioms EKClassicalPlactic.sigma_eq
#print axioms EKClassicalPlactic.sigma_eq_of_rows
#print axioms EKClassicalPlactic.le_foldr_max
#print axioms EKClassicalPlactic.rows_eq_P
#print axioms EKClassicalPlactic.inAlphabet_of_knuth
#print axioms EKClassicalPlactic.tableau_eq_of_knuth
#print axioms EKClassicalPlactic.theorem_4_1_insertion
#print axioms EKClassicalPlactic.theorem_4_1
#print axioms EKClassicalPlactic.knuthCon
#print axioms EKClassicalPlactic.knuthCon_eq_conGen
#print axioms EKClassicalPlactic.plSub
#print axioms EKClassicalPlactic.rowWord_pos
#print axioms EKClassicalPlactic.tabToPl
#print axioms EKClassicalPlactic.tabToPl_bijective
#print axioms EKClassicalPlactic.tabEquivPl
#print axioms EKClassicalPlactic.tableauBasis
#print axioms EKClassicalPlactic.tableauBasis_apply
#print axioms EKClassicalPlactic.controlWords_length
#print axioms EKClassicalPlactic.control_invariance
#print axioms EKClassicalPlactic.control_valid_fixed
#print axioms EKClassicalPlactic.control_existence
#print axioms EKClassicalPlactic.control_separation
#print axioms EKClassicalPlactic.wrong_variant_step
#print axioms EKClassicalPlactic.wrong_variant_breaks_uniqueness
#print axioms EKClassicalPlactic.wrong_variant_fails

end OddMath.Frontier.EKClassicalPlacticAudit

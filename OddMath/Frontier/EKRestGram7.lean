import OddMath.Frontier.EKRestData

/-! # The q = -1 Gram matrix in degree 7

EK arXiv:1107.5610v2, §5.2 (the q = -1 tables stop at degree 6). The Gram matrix
`EKDualBases.Mh 7` of the quotient pairing in the h-basis, lexicographic order, evaluated
entrywise by `EKRest.fastEval` (`gram_table7`). Used for the degree-7 counterexample in
`EKRestForgotten`.
-/

noncomputable section
set_option maxRecDepth 100000

namespace OddMath.Frontier.EKRest
open EKAppendixData DegreeShapes EKDualBases

/-- The fifteen partitions of 7, lexicographic order. -/
def pl7 : Fin 15 → List ℕ := ![[1,1,1,1,1,1,1], [2,1,1,1,1,1], [2,2,1,1,1], [2,2,2,1],
  [3,1,1,1,1], [3,2,1,1], [3,2,2], [3,3,1], [4,1,1,1], [4,2,1], [4,3], [5,1,1], [5,2],
  [6,1], [7]]

def hshapes7 : Fin 15 → DegreeShape 7 := ![
  ⟨YoungDiagram.ofRowLens [1,1,1,1,1,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [2,1,1,1,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [2,2,1,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [2,2,2,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,1,1,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,2,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,2,2] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,3,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [4,1,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [4,2,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [4,3] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [5,1,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [5,2] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [6,1] (by decide), card_yd _ _ 7 rfl⟩,
  ⟨YoungDiagram.ofRowLens [7] (by decide), card_yd _ _ 7 rfl⟩]

theorem hs7 : ∀ j, (hshapes7 j).val.rowLens = pl7 j := by
  intro j; fin_cases j <;> exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)

theorem exhaust7 : ∀ ν, ∃ j, ν = hshapes7 j := exhaust hshapes7 pl7 hs7 (by decide +kernel)

theorem inj7 : Function.Injective hshapes7 := inj_of_rowLens hshapes7 pl7 hs7 (by decide)

/-- The q = -1 Gram matrix in degree 7 (h-basis, lexicographic order). -/
def gram7 : Matrix (Fin 15) (Fin 15) ℤ := !![
  0, 0, 0, 6, 0, 0, 6, 0, 0, 3, 3, 0, 3, 1, 1;
  0, 0, 2, 0, 0, 2, 10, 2, 1, 0, 1, 1, 4, 0, 1;
  0, 2, 0, -9, 2, 6, 11, 4, 0, -4, -2, 2, 4, -1, 1;
  6, 0, -9, -16, 6, 9, 7, 5, -3, -8, -5, 3, 3, -2, 1;
  0, 0, 2, 6, 0, 2, 6, 2, 1, 3, 3, 1, 3, 1, 1;
  0, 2, 6, 9, 2, 3, 1, 4, 3, 5, 5, 2, 2, 2, 1;
  6, 10, 11, 7, 6, 1, -7, 5, 7, 6, 6, 3, 0, 3, 1;
  0, 2, 4, 5, 2, 4, 5, 4, 2, 3, 3, 2, 3, 1, 1;
  0, 1, 0, -3, 1, 3, 7, 2, 0, -1, 0, 1, 3, 0, 1;
  3, 0, -4, -8, 3, 5, 6, 3, -1, -4, -2, 2, 3, -1, 1;
  3, 1, -2, -5, 3, 5, 6, 3, 0, -2, 0, 2, 3, 0, 1;
  0, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 1;
  3, 4, 4, 3, 3, 2, 0, 3, 3, 3, 3, 2, 1, 2, 1;
  1, 0, -1, -2, 1, 2, 3, 1, 0, -1, 0, 1, 2, 0, 1;
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem gram7_symm : ∀ i j, gram7 i j = gram7 j i := by decide

theorem fast_table7 : ∀ i j, i ≤ j → fastH (pl7 i) (pl7 j) = gram7 i j := by
  decide +kernel

theorem gram_table7 : ∀ i j, Mh 7 (hshapes7 i) (hshapes7 j) = gram7 i j := by
  intro i j
  rcases le_total i j with h | h
  · rw [Mh_fast, hs7, hs7, fast_table7 i j h]
  · rw [Mh_symm, Mh_fast, hs7, hs7, fast_table7 j i h, gram7_symm]

end OddMath.Frontier.EKRest

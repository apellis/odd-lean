import OddMath.Frontier.EKRestEval
import OddMath.Frontier.EKCenterPower
import OddMath.Frontier.EKPresentationControls

/-! # EK finite data: the degree-6 table, Examples 2.7, 2.8, 3.2, and `e₄, e₅`

EK arXiv:1107.5610v2, integral q = -1, in the radical quotient `Q`.

* §5.2, p. 39: the printed q = -1 table of the bilinear form in degree 6
  (h-basis, printed order) is the Gram matrix `EKDualBases.Mh 6` (`gram_table6`).
* §2.2, p. 10: the printed expansions of `e₄` and `e₅` (`e_four`, `e_five`).
* §2.2, p. 13: Example 2.7, `(e₂h₁h₂, h₂e₃) = -1`, and Example 2.8, `(e₂h₂, e₂h₂) = -2`.
* §3.1, p. 24: Example 3.2, `M_{(3,2),(2,2,1)} = -1`, `M′ = 3`, `M″ = -1`.

All values are closed by kernel evaluation of the certified evaluator
`EKRest.fastEval` (`EKRestEval`).
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators

namespace OddMath.Frontier.EKRest
open EKRadicalQuotient EKAppendixData DegreeShapes EKDualBases EKIntegralBases

/-! ## Generic table transfer -/

theorem Mh_table {d k : ℕ} (S : Fin k → DegreeShape d) (pl : Fin k → List ℕ)
    (hS : ∀ j, (S j).val.rowLens = pl j) (G : Matrix (Fin k) (Fin k) ℤ)
    (hG : ∀ i j, fastH (pl i) (pl j) = G i j) : ∀ i j, Mh d (S i) (S j) = G i j := by
  intro i j; rw [Mh_fast, hS, hS, hG]

theorem M_table {d k : ℕ} (S : Fin k → DegreeShape d) (pl : Fin k → List ℕ)
    (hS : ∀ j, (S j).val.rowLens = pl j) (G : Matrix (Fin k) (Fin k) ℤ)
    (hG : ∀ i j, fastEH (pl i) (pl j) = G i j) : ∀ i j, M d (S i) (S j) = G i j := by
  intro i j; rw [M_fast, hS, hS, hG]

/-- `h_λ = h_{λ₁} ⋯ h_{λ_r}` for an explicit list. -/
def hP (l : List ℕ) : Q := (l.map EKElementaryQuotient.h).prod

theorem hPartition_eq_hP {d k : ℕ} (S : Fin k → DegreeShape d) (pl : Fin k → List ℕ)
    (hS : ∀ j, (S j).val.rowLens = pl j) (j : Fin k) :
    EKPartitionSpanning.hPartition (S j).val = hP (pl j) := by
  rw [EKPartitionSpanning.hPartition, hS, hP]

/-- Coefficient form of an `m_of_table` expansion, in `Q`. -/
theorem mBasis_val {d k : ℕ} (S : Fin k → DegreeShape d) (pl : Fin k → List ℕ)
    (hS : ∀ j, (S j).val.rowLens = pl j) (μ : DegreeShape d) (c : Fin k → ℤ)
    (h : mBasis d μ = ∑ l, c l • degreeHBasis d (S l)) :
    ((mBasis d μ : degreePiece d) : Q) = ∑ l, c l • hP (pl l) := by
  rw [h, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Submodule.coe_smul, degreeHBasis_apply, hPartition_eq_hP S pl hS]

/-! ## §5.2, p. 39: the q = -1 table in degree 6 -/

/-- Printed degree-6 h-basis, printed order
h111111, h21111, h2211, h222, h3111, h321, h33, h411, h42, h51, h6. -/
def hshapes6 : Fin 11 → DegreeShape 6 := ![
  ⟨YoungDiagram.ofRowLens [1,1,1,1,1,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [2,1,1,1,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [2,2,1,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [2,2,2] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,1,1,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,2,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [3,3] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [4,1,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [4,2] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [5,1] (by decide), card_yd _ _ 6 rfl⟩,
  ⟨YoungDiagram.ofRowLens [6] (by decide), card_yd _ _ 6 rfl⟩]

def pl6 : Fin 11 → List ℕ := ![[1,1,1,1,1,1], [2,1,1,1,1], [2,2,1,1], [2,2,2], [3,1,1,1],
  [3,2,1], [3,3], [4,1,1], [4,2], [5,1], [6]]

theorem hs6 : ∀ j, (hshapes6 j).val.rowLens = pl6 j := by
  intro j; fin_cases j <;> exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)

/-- The printed degree-6 list is all shapes of degree 6. -/
theorem exhaust6 : ∀ ν, ∃ j, ν = hshapes6 j := exhaust hshapes6 pl6 hs6 (by decide +kernel)

theorem inj6 : Function.Injective hshapes6 := inj_of_rowLens hshapes6 pl6 hs6 (by decide)

/-- EK §5.2, p. 39: the printed q = -1 table in degree 6, verbatim. -/
def printedGram6 : Matrix (Fin 11) (Fin 11) ℤ := !![
  0, 0, 0, 6, 0, 0, 0, 0, 3, 0, 1;
  0, 0, 2, 6, 0, 2, 2, 1, 3, 1, 1;
  0, 2, 4, 3, 2, 4, 4, 2, 2, 2, 1;
  6, 6, 3, -3, 6, 5, 5, 3, 0, 3, 1;
  0, 0, 2, 6, 0, -1, 0, 1, 3, 0, 1;
  0, 2, 4, 5, -1, -4, -2, 2, 3, -1, 1;
  0, 2, 4, 5, 0, -2, 0, 2, 3, 0, 1;
  0, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1;
  3, 3, 2, 0, 3, 3, 3, 2, 1, 2, 1;
  0, 1, 2, 3, 0, -1, 0, 1, 2, 0, 1;
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem fast_table6 : ∀ i j, fastH (pl6 i) (pl6 j) = printedGram6 i j := by
  decide +kernel

/-- **EK §5.2, p. 39, degree 6.** Every printed entry of the q = -1 table equals the
Gram matrix `Mh 6` of the actual quotient pairing in the h-basis. -/
theorem gram_table6 : ∀ i j, Mh 6 (hshapes6 i) (hshapes6 j) = printedGram6 i j :=
  Mh_table hshapes6 pl6 hs6 printedGram6 fast_table6

/-! ## §2.2, p. 13: Examples 2.7 and 2.8 -/

/-- A mixed word given as a list of (colour, part) pairs. -/
def cw (l : List (Bool × ℕ)) : Q := (l.map (fun p => col p.1 p.2)).prod

theorem pairing_cw (a b : List (Bool × ℕ)) :
    quotientPairing (cw a) (cw b) =
      fastEval (a.map Prod.snd) (a.map Prod.fst) (b.map Prod.snd) (b.map Prod.fst) := by
  have hm : ∀ l : List (Bool × ℕ),
      EKMixedPairing.mixed (fun i : Fin l.length => (l.get i).2) (fun i => (l.get i).1) = cw l := by
    intro l
    rw [EKMixedPairing.mixed, cw]
    congr 1
    apply List.ext_get (by simp)
    intro n h1 h2
    simp [col]
  have ho : ∀ {α β : Type} (l : List α) (f : α → β), List.ofFn (fun i : Fin l.length => f (l.get i)) =
      l.map f := by
    intro α β l f
    apply List.ext_get (by simp)
    intro n h1 h2
    simp
  rw [← hm a, ← hm b, quotientPairing_mixed_fastEval, ho, ho, ho, ho]

open EKElementaryQuotient in
/-- **EK Example 2.7, p. 13:** `(e₂h₁h₂, h₂e₃) = -1`. -/
theorem example_2_7 : quotientPairing (e 2 * h 1 * h 2) (h 2 * e 3) = -1 := by
  have h1 : e 2 * h 1 * h 2 = cw [(true, 2), (false, 1), (false, 2)] := by simp [cw, col, mul_assoc]
  have h2 : h 2 * e 3 = cw [(false, 2), (true, 3)] := by simp [cw, col]
  rw [h1, h2, pairing_cw]
  decide +kernel

open EKElementaryQuotient in
/-- **EK Example 2.8, p. 13:** `(e₂h₂, e₂h₂) = -2`. -/
theorem example_2_8 : quotientPairing (e 2 * h 2) (e 2 * h 2) = -2 := by
  have h1 : e 2 * h 2 = cw [(true, 2), (false, 2)] := by simp [cw, col]
  rw [h1, pairing_cw]
  decide +kernel

/-! ## §3.1, p. 24: Example 3.2 -/

def shape32 : DegreeShape 5 := ⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩
def shape221 : DegreeShape 5 := ⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩

theorem shape32_rows : shape32.val.rowLens = [3,2] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
theorem shape221_rows : shape221.val.rowLens = [2,2,1] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)

/-- **EK Example 3.2, p. 24:** `M_{(3,2),(2,2,1)} = -1`, `M′_{(3,2),(2,2,1)} = 3`,
`M″_{(3,2),(2,2,1)} = -1`, for the matrices of (3.2) (`M = (e_λ, h_μ)`, `M′ = (h_λ, h_μ)`,
`M″ = (e_λ, e_μ)`, whose matrix-count descriptions are Proposition 3.1,
`EKDualBases.proposition_3_1_M/_Mh/_Me`). -/
theorem example_3_2 : M 5 shape32 shape221 = -1 ∧ Mh 5 shape32 shape221 = 3 ∧
    Me 5 shape32 shape221 = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [M_fast, shape32_rows, shape221_rows]; decide +kernel
  · rw [Mh_fast, shape32_rows, shape221_rows]; decide +kernel
  · rw [Me_fast, shape32_rows, shape221_rows]; decide +kernel

/-! ## §2.2, p. 10: the printed `e₄` and `e₅` -/

section eExpansions
open EKElementaryQuotient EKPresentationControls

/-- The defining recurrence (2.5) in degree 4, expanded. -/
theorem recurrence_four :
    h 4 + (-(e 1 * h 3) + (-(e 2 * h 2) + (e 3 * h 1 + e 4))) = 0 := by
  have hh := congrArg pi (CompleteElementary.elementary_complete_inverse 3)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, map_add, map_mul,
    map_zero] at hh
  norm_num [CompleteElementary.ekSign, show Nat.choose 4 2 = 6 from rfl,
    show Nat.choose 5 2 = 10 from rfl] at hh
  exact hh

/-- The defining recurrence (2.5) in degree 5, expanded. -/
theorem recurrence_five :
    h 5 + (-(e 1 * h 4) + (-(e 2 * h 3) + (e 3 * h 2 + (e 4 * h 1 + -e 5)))) = 0 := by
  have hh := congrArg pi (CompleteElementary.elementary_complete_inverse 4)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, map_add, map_mul,
    map_zero] at hh
  norm_num [CompleteElementary.ekSign, show Nat.choose 4 2 = 6 from rfl,
    show Nat.choose 5 2 = 10 from rfl, show Nat.choose 6 2 = 15 from rfl] at hh
  exact hh

theorem h1_h3 : h 1 * h 3 - h 3 * h 1 = 0 :=
  sub_eq_zero.mpr (EKQuotientRelations.complete_even 1 3 (by decide))

theorem h11_h2 : h 1 * h 1 * h 2 - h 2 * (h 1 * h 1) = 0 :=
  sub_eq_zero.mpr EKCenterPowerControls.h11_comm_h2

theorem h11_h3 : h 1 * h 1 * h 3 - h 3 * (h 1 * h 1) = 0 :=
  sub_eq_zero.mpr EKCenterPowerControls.h11_comm_h3

theorem h1_h2 : h 1 * h 2 + h 2 * h 1 - (2 : ℤ) • h 3 = 0 := by
  have := EKQuotientRelations.complete_one_even 1
  simp only [Nat.mul_one] at this
  rw [this, sub_self]

theorem h3_h2 : h 3 * h 2 - h 2 * h 3 - h 1 * h 4 + h 4 * h 1 = 0 := by
  have := EKQuotientRelations.complete_odd 3 2 (by decide) (by decide)
  norm_num at this
  rw [show h 3 * h 2 - h 2 * h 3 - h 1 * h 4 + h 4 * h 1 =
    (h 3 * h 2 + -(h 2 * h 3)) - (-(h 4 * h 1) + h 1 * h 4) by noncomm_ring, this, sub_self]

/-- **EK p. 10:** `e₄ = -h₄ + h₂² - h₂h₁² + h₁⁴`. -/
theorem e_four : e 4 = -h 4 + h 2 * h 2 - h 2 * h 1 * h 1 + h 1 * h 1 * h 1 * h 1 := by
  rw [← sub_eq_zero]
  calc e 4 - (-h 4 + h 2 * h 2 - h 2 * h 1 * h 1 + h 1 * h 1 * h 1 * h 1)
      = (h 4 + (-(e 1 * h 3) + (-(e 2 * h 2) + (e 3 * h 1 + e 4)))) +
          (h 1 * h 3 - h 3 * h 1) - (h 1 * h 1 * h 2 - h 2 * (h 1 * h 1)) := by
        rw [degree_one, degree_two, degree_three]; noncomm_ring
    _ = 0 := by rw [recurrence_four, h1_h3, h11_h2]; simp

set_option maxHeartbeats 2000000 in
/-- **EK p. 10:** `e₅ = h₅ - 2h₄h₁ - h₃h₁² + h₂²h₁ + h₁⁵`. -/
theorem e_five : e 5 = h 5 - (2 : ℤ) • (h 4 * h 1) - h 3 * h 1 * h 1 + h 2 * h 2 * h 1 +
    h 1 * h 1 * h 1 * h 1 * h 1 := by
  rw [← sub_eq_zero]
  calc e 5 - (h 5 - (2 : ℤ) • (h 4 * h 1) - h 3 * h 1 * h 1 + h 2 * h 2 * h 1 +
        h 1 * h 1 * h 1 * h 1 * h 1)
      = -(h 5 + (-(e 1 * h 4) + (-(e 2 * h 3) + (e 3 * h 2 + (e 4 * h 1 + -e 5))))) +
          (h 3 * h 2 - h 2 * h 3 - h 1 * h 4 + h 4 * h 1) +
          (h 1 * h 1 * h 3 - h 3 * (h 1 * h 1)) - h 1 * (h 1 * h 1 * h 2 - h 2 * (h 1 * h 1)) -
          (h 1 * h 2 + h 2 * h 1 - (2 : ℤ) • h 3) * h 1 * h 1 := by
        rw [degree_one, degree_two, degree_three, e_four]; noncomm_ring
    _ = 0 := by rw [recurrence_five, h3_h2, h11_h3, h11_h2, h1_h2]; simp

end eExpansions

end OddMath.Frontier.EKRest

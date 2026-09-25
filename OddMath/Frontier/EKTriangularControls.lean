import OddMath.Frontier.EKAutomorphismsControls
import OddMath.Frontier.EKTriangular
noncomputable section
namespace OddMath.Frontier.EKTriangularControls
open EKRadicalQuotient EKElementaryQuotient EKAutomorphisms
open EKIntegralBases EKPartitionSpanning EKIntegralBasesControls

theorem empty_word : psi3 (([].map h).prod) = 1 := by
  simpa [pairExponent] using psi3_hWord []

theorem one_row (n : ℕ) : psi3 (h n) = h n := psi3_h n

theorem repeated_parts : psi3 (h 1*h 1) = -(h 1*h 1) :=
  EKAutomorphismsControls.super_square

theorem repeated_even : psi3 (h 2*h 2) = h 2*h 2 := by
  simpa [pairExponent] using psi3_hWord [2,2]

theorem first_noncommuting :
    hBasis.repr (psi3 (hPartition shape21)) =
      Finsupp.single row3 2 - Finsupp.single shape21 1 := by
  rw [shape21_value, EKAutomorphismsControls.psi3_reverses_noncommuting_word.1]
  exact degree_three_coordinates

theorem direction : List.Lex (· < ·) shape21.rowLens row3.rowLens := by
  have h21 : shape21.rowLens = [2,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have h3 : row3.rowLens = [3] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  rw [h21, h3]
  exact List.Lex.rel (by decide)

theorem wrong_reversal_rejected : psi3 (h 1*h 1) ≠ h 1*h 1 :=
  EKAutomorphismsControls.ordinary_reversal_rejected

theorem wrong_diagonal_rejected : hBasis.repr (psi3 (hPartition col2)) col2 ≠ 1 := by
  rw [col2_value, repeated_parts, ← col2_value, map_neg, h_coordinates_partition]
  simp

theorem wrong_lower_direction_rejected :
    hBasis.repr (psi3 (hPartition shape21)) row3 ≠ 0 := by
  have hn : shape21 ≠ row3 := by
    intro he
    have hr := congrArg YoungDiagram.rowLens he
    have h21 : shape21.rowLens = [2,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
    have h3 : row3.rowLens = [3] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
    rw [h21, h3] at hr
    contradiction
  rw [first_noncommuting]
  simp [hn]

/- Degree-four mixed [3,1] was hand-checked during initial inspection:
psi3(h3*h1)=-h1*h3=-h3*h1 by the even-sum relation.
Its first compiled check is POST-production; do not backdate it. -/
theorem mixed_degree_four : psi3 (h 3*h 1)=-(h 3*h 1) := by
  have hh : h 1*h 3=h 3*h 1 := EKQuotientRelations.same_even false 1 3 (by decide)
  have hs := psi3_hWord [3,1]
  simpa [pairExponent, hh] using hs

def shape22 : YoungDiagram := YoungDiagram.ofRowLens [2,2] (by decide)
def shape31 : YoungDiagram := YoungDiagram.ofRowLens [3,1] (by decide)

theorem source_diagonal_sign_controls :
    (-1 : ℤ)^(EKTriangular.b empty.transpose)=1 ∧
    (-1 : ℤ)^(EKTriangular.b col2.transpose) = -1 ∧
    (-1 : ℤ)^(EKTriangular.b shape21.transpose) = -1 ∧
    (-1 : ℤ)^(EKTriangular.b shape22.transpose) = 1 ∧
    (-1 : ℤ)^(EKTriangular.b shape31.transpose) = -1 := by
  have h0 : empty.rowLens=[] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have h11 : col2.rowLens=[1,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have h21 : shape21.rowLens=[2,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have h22 : shape22.rowLens=[2,2] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have h31 : shape31.rowLens=[3,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  simp [EKTriangular.b_transpose, h0, h11, h21, h22, h31, cost]

theorem wrong_degree_coordinate : hBasis.repr (psi3 (hPartition shape21)) col2=0 := by
  apply EKTriangular.psi3_coordinate_zero
  left
  change (YoungDiagram.cellsOfRowLens [1,1]).card ≠ (YoungDiagram.cellsOfRowLens [2,1]).card
  rw [card_cellsOfRowLens, card_cellsOfRowLens]
  decide

/-- Literal printed (2.24), with j,j, remains false; it is not used. -/
theorem printed_224_still_rejected : psi3 (h 2*h 1)≠-(h 1*h 2) :=
  EKAutomorphismsControls.literal_printed_224_counterexample

/-- All partitions and all coordinates, not a small rank substitute. -/
theorem general_consumer (μ ν : YoungDiagram) :
    psi3 (hPartition μ) ∈ EKTriangular.Hge μ ∧
    hBasis.repr (psi3 (hPartition μ)) μ=(-1 : ℤ)^(EKTriangular.b μ.transpose) ∧
    (ν.card≠μ.card ∨ ¬ (ν=μ ∨ List.Lex (· < ·) μ.rowLens ν.rowLens) →
      hBasis.repr (psi3 (hPartition μ)) ν=0) :=
  ⟨EKTriangular.psi3_mem_Hge μ, EKTriangular.psi3_diagonal μ,
    EKTriangular.psi3_coordinate_zero μ ν⟩

end OddMath.Frontier.EKTriangularControls

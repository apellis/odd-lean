import OddMath.Frontier.EKIntegralBases
import OddMath.Frontier.EKSemiorthogonality

/-! Test-first controls. Hand calculations: e₂=h₂-h₁² and
h₁h₂=2h₃-h₂h₁; the empty word is the degree-zero unit.
No production module exists when these controls are first checked. -/
noncomputable section
namespace OddMath.Frontier.EKIntegralBasesControls
open EKRadicalQuotient EKElementaryQuotient

def empty : YoungDiagram := YoungDiagram.ofRowLens [] (by decide)
def row2 : YoungDiagram := YoungDiagram.ofRowLens [2] (by decide)
def col2 : YoungDiagram := YoungDiagram.ofRowLens [1,1] (by decide)
def row3 : YoungDiagram := YoungDiagram.ofRowLens [3] (by decide)
def shape21 : YoungDiagram := YoungDiagram.ofRowLens [2,1] (by decide)

 theorem unit_control : EKPartitionSpanning.hPartition empty = 1 ∧
    EKPartitionSpanning.ePartition empty = 1 := by
  simp [EKPartitionSpanning.hPartition, EKPartitionSpanning.ePartition, empty,
    YoungDiagram.rowLens_ofRowLens_eq_self (by simp : ∀ a ∈ ([] : List ℕ), 0 < a)]

theorem degree_zero_word : EKFreeCoproduct.degree (1 : EKFreeCoproduct.W) = 0 ∧
    pi (EKFreeCoproduct.wordBasis 1) = 1 := by simp

theorem elementary_two : e 2 = h 2 - h 1 * h 1 := by
  unfold e h
  have he : CompleteElementary.elementary 2 =
      CompleteElementary.h 2 - CompleteElementary.h 1 * CompleteElementary.h 1 := by
    simp [CompleteElementary.elementary, CompleteElementary.ekSign,
      CompleteElementary.inverseCoeff, Fin.sum_univ_succ, pow_succ, sub_eq_add_neg]
  rw [he, map_sub, map_mul]

theorem degree_three_sign : h 1 * h 2 = (2 : ℤ) • h 3 - h 2 * h 1 := by
  have hh := EKQuotientRelations.same_odd_succ false 0 2 (by decide)
  apply eq_sub_iff_add_eq.mpr
  simpa [two_smul, EKMixedPairing.gen, h] using hh.symm

theorem distinct_degree_two_partitions :
    EKPartitionSpanning.hPartition row2 ≠ EKPartitionSpanning.hPartition col2 := by
  intro hh
  have he := EKSemiorthogonality.hPartition_linearIndependent.injective hh
  have hc := congrArg YoungDiagram.rowLens he
  have hr : row2.rowLens = [2] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  have hv : col2.rowLens = [1,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  rw [hr, hv] at hc
  contradiction

/- The following basis/decomposition consumers are POST-production checks.
The explicit integral linear combinations above were checked first. -/
open EKIntegralBases
open EKPartitionSpanning (hPartition ePartition)

@[simp] theorem row2_value : hPartition row2 = h 2 := by
  have hr : row2.rowLens = [2] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  simp [hPartition, hr]
@[simp] theorem col2_value : hPartition col2 = h 1 * h 1 := by
  have hr : col2.rowLens = [1,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  simp [hPartition, hr]
@[simp] theorem row3_value : hPartition row3 = h 3 := by
  have hr : row3.rowLens = [3] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  simp [hPartition, hr]
@[simp] theorem shape21_value : hPartition shape21 = h 2 * h 1 := by
  have hr : shape21.rowLens = [2,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
  simp [hPartition, hr]

theorem degree_two_coordinates :
    hBasis.repr (e 2) = Finsupp.single row2 1 - Finsupp.single col2 1 := by
  rw [elementary_two, ← row2_value, ← col2_value, map_sub,
    h_coordinates_partition, h_coordinates_partition]

theorem degree_three_coordinates :
    hBasis.repr (h 1 * h 2) = Finsupp.single row3 2 - Finsupp.single shape21 1 := by
  rw [degree_three_sign, ← row3_value, ← shape21_value, map_sub, map_smul,
    h_coordinates_partition, h_coordinates_partition]
  simp

/-- Deliberately wrong degree-two sign is false in the actual quotient. -/
theorem wrong_elementary_sign_rejected : e 2 ≠ h 2 + h 1 * h 1 := by
  intro he
  have hh := congrArg (fun x : Q => hBasis.repr x col2) he
  have hn : row2 ≠ col2 := by
    intro hrc
    exact distinct_degree_two_partitions (congrArg hPartition hrc)
  dsimp only at hh
  rw [degree_two_coordinates, ← row2_value, ← col2_value, map_add,
    h_coordinates_partition, h_coordinates_partition] at hh
  simp [hn] at hh

/-- The source's noncommuting degree-three word does not have swapped coordinates. -/
theorem wrong_degree_three_swap_rejected : h 1 * h 2 ≠ h 2 * h 1 := by
  intro he
  have hh := congrArg (fun x : Q => hBasis.repr x row3) he
  have hn : shape21 ≠ row3 := by
    intro heq
    have hr : shape21.rowLens = [2,1] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
    have hs : row3.rowLens = [3] := YoungDiagram.rowLens_ofRowLens_eq_self (by simp)
    have hc := congrArg YoungDiagram.rowLens heq
    rw [hr, hs] at hc
    contradiction
  dsimp only at hh
  rw [degree_three_coordinates, ← shape21_value, h_coordinates_partition] at hh
  simp [hn] at hh

theorem exact_unit_decomposition : decompose (1 : Q) = Finsupp.single 0 1 := decompose_unit

theorem inhomogeneous_control :
    decompose (1 + h 2 + h 1 * h 2) =
      Finsupp.single 0 1 + Finsupp.single 2 (h 2) + Finsupp.single 3 (h 1 * h 2) := by
  have h2 : h 2 ∈ degreePiece 2 := by
    rw [degreePiece_eq_hPartition_span]
    exact generator_mem false 2
  have h1 : h 1 ∈ degreePiece 1 := by
    rw [degreePiece_eq_hPartition_span]
    exact generator_mem false 1
  have h12 : h 1 * h 2 ∈ degreePiece 3 := degreePiece_mul (a := 1) (b := 2) h1 h2
  rw [map_add, map_add, decompose_unit, decompose_piece h2, decompose_piece h12]

/-- A rank/unicity consumer at an arbitrary degree, not another finite ladder. -/
theorem arbitrary_degree_consumer (d : ℕ) (x : degreePiece d) :
    letI := DegreeShapes.degreeFintype d
    Module.finrank ℤ (degreePiece d) = Fintype.card (DegreeShapes.DegreeShape d) ∧
      (∃! a : DegreeShapes.DegreeShape d → ℤ,
        ∑ μ, a μ • ePartition μ.val = (x : Q)) :=
  ⟨degree_finrank d, degree_e_unique_coordinates d x⟩

end OddMath.Frontier.EKIntegralBasesControls

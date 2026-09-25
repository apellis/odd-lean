import OddMath.Frontier.EKDualBasesControls
import OddMath.Frontier.EKQuotientRelations

/-! PRE-production hand controls for EK 1107.5610v2 Prop 3.4 (printed pp25–26),
integral q = -1, in the actual radical quotient `Q`.

`p_k` is the integral dual `(mBasis k (k)).val` of the one-row complete element.
Hand fixtures (source p25 list): p1 = h1, p2 = h1 h1, p3 = h111 + h21 - h3,
p4 = -h1111 - 2 h22 + 4 h4.  Only p1 and p2 are machine-checked here; p3 and
p4 were checked by exact Python Gram computation (an unpublished script), not in Lean.
Control k=1: p1 does not commute with h2.  Control k=2: p2 commutes with every
h-word all of whose parts are ≤ 3 (in particular every degree ≤ 3 h-word).
The two-letter product expansion below is the source coproduct (2.10) plus
adjointness; it is reused by production. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKCenterPowerControls
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient
open EKPairingMatrices

/-- Left-product expansion against an arbitrary platform word. -/
theorem pairing_mul_word {r : ℕ} (P Y : A) (β : Fin r → ℕ) (η : Fin r → Bool) :
    pairing (P * Y) (EKMixedPairing.word β η) =
      ∑ u : Splits β, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
        (pairing P (EKMixedPairing.word (upper u) η) *
          pairing Y (EKMixedPairing.word (lower u) η)) := by
  rw [← adjointness, EKMixedPairing.coproduct_word]
  simp only [map_sum, map_smul, tensorPairing_tmul, smul_eq_mul]

theorem word_two (a b : ℕ) :
    EKMixedPairing.word ![a, b] ![false, false] = CompleteElementary.h a * CompleteElementary.h b := by
  simp [EKMixedPairing.word, EKMixedPairing.gen, List.ofFn_succ]

theorem sum_splits_succ {c : ℕ} (α : Fin (c+1) → ℕ) (f : Splits α → ℤ) :
    ∑ u, f u = ∑ i : Fin (α 0+1), ∑ u : Splits (fun j => α j.succ), f (Fin.insertNth 0 i u) := by
  rw [← (Fin.insertNthEquiv (fun j => Fin (α j+1)) 0).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

theorem sum_splits_zero (α : Fin 0 → ℕ) (f : Splits α → ℤ) :
    ∑ u, f u = f (fun i => Fin.elim0 i) := Fintype.sum_unique f

/-- Two-letter right argument, all indices explicit, crossing sign `j*(a-i)`. -/
theorem pairing_mul_two (P Y : A) (a b : ℕ) :
    pairing (P * Y) (CompleteElementary.h a * CompleteElementary.h b) =
      ∑ i : Fin (a+1), ∑ j : Fin (b+1), (-1 : ℤ) ^ (j.val * (a - i.val)) *
        (pairing P (CompleteElementary.h i.val * CompleteElementary.h j.val) *
          pairing Y (CompleteElementary.h (a - i.val) * CompleteElementary.h (b - j.val))) := by
  have hh := pairing_mul_word P Y ![a, b] ![false, false]
  simp only [sum_splits_succ, sum_splits_zero] at hh
  rw [word_two] at hh
  simpa [EKMixedPairing.word, List.ofFn_succ, crossCols, upper, lower, Fin.sum_univ_succ,
    Fin.insertNth_zero, EKMixedPairing.gen] using hh

theorem pairing_h_two (n i j : ℕ) :
    pairing (CompleteElementary.h n) (CompleteElementary.h i * CompleteElementary.h j) =
      if n = i + j then 1 else 0 := by
  have hh := EKMixedPairing.pairing_gen_word n false ![i, j] ![false, false]
  rw [word_two] at hh
  simpa [EKMixedPairing.gen, EKMixedPairing.cell, Fin.sum_univ_two] using hh

/-- Hand values in degree 3. -/
theorem h12_h12 : pairing (CompleteElementary.h 1 * CompleteElementary.h 2)
    (CompleteElementary.h 1 * CompleteElementary.h 2) = 0 := by
  rw [pairing_mul_two]
  simp [pairing_h_two, Fin.sum_univ_succ]

theorem h12_h21 : pairing (CompleteElementary.h 1 * CompleteElementary.h 2)
    (CompleteElementary.h 2 * CompleteElementary.h 1) = 2 := by
  rw [pairing_mul_two]
  simp [pairing_h_two, Fin.sum_univ_succ]

local notation "hq" => EKElementaryQuotient.h

theorem h1h2_ne_h2h1 : hq 1 * hq 2 ≠ hq 2 * hq 1 := by
  intro he
  have hc := congrArg (quotientPairing (pi (CompleteElementary.h 1 * CompleteElementary.h 2))) he
  simp only [EKElementaryQuotient.h, ← map_mul, quotientPairing_pi, h12_h12, h12_h21] at hc
  omega

open EKDualBases EKIntegralBases DegreeShapes
open EKPartitionSpanning (hPartition)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

def row1 : DegreeShape 1 :=
  ⟨YoungDiagram.ofRowLens [1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩

@[simp] theorem row1_rows : row1.val.rowLens = [1] :=
  by exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)

theorem degree_one_shape (μ : DegreeShape 1) : μ = row1 := by
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change μ.val.rowLens = row1.val.rowLens
  rw [row1_rows]
  have hs := (rowLens_sum μ.val).trans μ.property
  have hp := μ.val.pos_of_mem_rowLens
  cases he : μ.val.rowLens with
  | nil => simp [he] at hs
  | cons a t =>
    have ha := hp a (by simp [he])
    cases t with
    | nil => simp only [he, List.sum_cons, List.sum_nil] at hs; simp; omega
    | cons b t =>
      have hb := hp b (by simp [he])
      simp only [he, List.sum_cons] at hs
      omega

/-- Fixture p1 = h1. -/
theorem p1_fixture : (mBasis 1 row1 : Q) = hq 1 := by
  have hmem : hq 1 ∈ degreePiece 1 := by
    rw [degreePiece_eq_hPartition_span]
    simpa [EKMixedPairing.gen, EKElementaryQuotient.h] using generator_mem false 1
  have hm : (⟨hq 1, hmem⟩ : degreePiece 1) = mBasis 1 row1 := m_unique 1 row1 _ (by
    intro ν; rw [degree_one_shape ν]
    simp [hPartition, EKDualBasesControls.degree_one])
  exact (congrArg Subtype.val hm).symm

/-- Fixture p2 = h1 h1 (the one-row degree-two shape of EKDualBasesControls). -/
theorem p2_fixture : (mBasis 2 EKDualBasesControls.row2 : Q) = hq 1 * hq 1 :=
  EKDualBasesControls.degree_two_duals.1

/-- Control k=1: an explicit non-commuting partner. -/
theorem control_k1 : (mBasis 1 row1 : Q) * hq 2 ≠ hq 2 * (mBasis 1 row1 : Q) := by
  rw [p1_fixture]; exact h1h2_ne_h2h1

theorem h11_comm_h1 : hq 1 * hq 1 * hq 1 = hq 1 * (hq 1 * hq 1) := by rw [mul_assoc]

theorem h11_comm_h2 : hq 1 * hq 1 * hq 2 = hq 2 * (hq 1 * hq 1) := by
  have e1 : hq 1 * hq 2 = (2 : ℤ) • hq 3 - hq 2 * hq 1 := by
    have := EKQuotientRelations.complete_one_even 1
    simp only [Nat.mul_one] at this
    exact eq_sub_of_add_eq this
  have e3 : hq 1 * hq 3 = hq 3 * hq 1 := EKQuotientRelations.complete_even 1 3 (by decide)
  rw [mul_assoc, e1, mul_sub, ← mul_assoc, e1, sub_mul, mul_smul_comm, smul_mul_assoc, e3]
  simp only [mul_assoc]
  abel

theorem h11_comm_h3 : hq 1 * hq 1 * hq 3 = hq 3 * (hq 1 * hq 1) := by
  have e3 : hq 1 * hq 3 = hq 3 * hq 1 := EKQuotientRelations.complete_even 1 3 (by decide)
  rw [mul_assoc, e3, ← mul_assoc, e3, mul_assoc]

theorem h11_comm_le3 (n : ℕ) (hn : n ≤ 3) : hq 1 * hq 1 * hq n = hq n * (hq 1 * hq 1) := by
  interval_cases n
  · simp [EKElementaryQuotient.h, CompleteElementary.h]
  · exact h11_comm_h1
  · exact h11_comm_h2
  · exact h11_comm_h3

/-- Control k=2: p2 commutes with every h-word with parts ≤ 3, hence with every
h-word of degree ≤ 3. -/
theorem control_k2 (α : List ℕ) (hα : ∀ a ∈ α, a ≤ 3) :
    (mBasis 2 EKDualBasesControls.row2 : Q) * pi (hWord α) =
      pi (hWord α) * (mBasis 2 EKDualBasesControls.row2 : Q) := by
  rw [p2_fixture]
  induction α with
  | nil => simp [hWord]
  | cons a t ih =>
    have ht := ih (fun b hb => hα b (by simp [hb]))
    have ha := h11_comm_le3 a (hα a (by simp))
    simp only [hWord, List.map_cons, List.prod_cons, map_mul] at ht ⊢
    change hq 1 * hq 1 * (hq a * pi (t.map CompleteElementary.h).prod) =
      hq a * pi (t.map CompleteElementary.h).prod * (hq 1 * hq 1)
    rw [← mul_assoc, ha, mul_assoc, ht, mul_assoc]

theorem control_k2_degree_le3 (α : List ℕ) (hα : α.sum ≤ 3) :
    (mBasis 2 EKDualBasesControls.row2 : Q) * pi (hWord α) =
      pi (hWord α) * (mBasis 2 EKDualBasesControls.row2 : Q) :=
  control_k2 α (fun _ ha => le_trans (List.le_sum_of_mem ha) hα)

end OddMath.Frontier.EKCenterPowerControls

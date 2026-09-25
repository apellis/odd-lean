import OddMath.Frontier.EKIntegralBases
import OddMath.Frontier.EKDualBases

/-! PRE-production hand controls: in the order (2),(1,1),
Mh = [[1,1],[1,0]], M = [[0,1],[1,0]], Me = [[-1,1],[1,0]].
Thus m₂=h₁², m₁₁=h₂-h₁²=e₂; f₂=h₁², f₁₁=h₂.
Empty and degree-one forms have the single entry 1. -/
noncomputable section
namespace OddMath.Frontier.EKDualBasesControls
open EKRadicalQuotient EKElementaryQuotient

theorem empty_pairing : quotientPairing (1 : Q) 1 = 1 := by
  change quotientPairing (pi 1) (pi 1) = 1
  rw [quotientPairing_pi]
  simp [EKPairingAdjoint.pairing_one]

theorem degree_one : quotientPairing (h 1) (h 1) = 1 := by
  simp [h]

theorem degree_two_hh : quotientPairing (h 2) (h 2) = 1 := by
  simp [h]

theorem degree_two_eh : quotientPairing (e 2) (h 2) = 0 := by
  simpa [EKMixedPairing.gen, e, h, EKMixedPairing.cell] using
    EKMixedPairing.pairing_gen_self true false 2

theorem degree_two_ee : quotientPairing (e 2) (e 2) = -1 := by
  simpa [EKMixedPairing.gen, e, EKMixedPairing.cell] using
    EKMixedPairing.pairing_gen_self true true 2

theorem elementary_two : e 2 = h 2 - h 1 * h 1 := by
  unfold e h
  have he : CompleteElementary.elementary 2 =
      CompleteElementary.h 2 - CompleteElementary.h 1 * CompleteElementary.h 1 := by
    simp [CompleteElementary.elementary, CompleteElementary.ekSign,
      CompleteElementary.inverseCoeff, Fin.sum_univ_succ, pow_succ, sub_eq_add_neg]
  rw [he, map_sub, map_mul]

theorem degree_two_h_h11 : quotientPairing (h 2) (h 1 * h 1) = 1 := by
  have hh := degree_two_eh
  rw [elementary_two, map_sub, LinearMap.sub_apply, degree_two_hh,
    quotientPairing_symm (h 1 * h 1) (h 2)] at hh
  omega

theorem degree_two_h11_h11 : quotientPairing (h 1 * h 1) (h 1 * h 1) = 0 := by
  have hh := degree_two_ee
  rw [elementary_two] at hh
  simp only [map_sub, LinearMap.sub_apply, degree_two_hh, degree_two_h_h11,
    quotientPairing_symm (h 1 * h 1) (h 2)] at hh
  omega

/- POST-production controls start here. Earlier test-first receipts precede
both the production file and its added import above. -/
open EKDualBases EKIntegralBases DegreeShapes
open EKPartitionSpanning (hPartition ePartition)
open scoped BigOperators
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- Literal empty and the two exhaustive degree-two partitions. -/
def emptyShape : DegreeShape 0 :=
  ⟨YoungDiagram.ofRowLens [] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
def row2 : DegreeShape 2 :=
  ⟨YoungDiagram.ofRowLens [2] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩
def col2 : DegreeShape 2 :=
  ⟨YoungDiagram.ofRowLens [1,1] (by decide), by rw [EKPartitionSpanning.card_ofRowLens]; rfl⟩

@[simp] theorem empty_rows : emptyShape.val.rowLens = [] :=
  by exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem row2_rows : row2.val.rowLens = [2] :=
  by exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem col2_rows : col2.val.rowLens = [1,1] :=
  by exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)

private theorem rows_ext {d : ℕ} {μ ν : DegreeShape d}
    (h : μ.val.rowLens = ν.val.rowLens) : μ = ν := by
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext h

theorem degree_zero_shape (μ : DegreeShape 0) : μ = emptyShape := by
  apply rows_ext
  rw [empty_rows]
  have hs := (rowLens_sum μ.val).trans μ.property
  cases he : μ.val.rowLens with
  | nil => rfl
  | cons a t =>
    have hp := μ.val.pos_of_mem_rowLens a (by simp [he])
    simp only [he, List.sum_cons] at hs
    omega

/-- Exhaustiveness, not just two chosen example partitions. -/
theorem degree_two_shapes (μ : DegreeShape 2) : μ = row2 ∨ μ = col2 := by
  have hs := (rowLens_sum μ.val).trans μ.property
  have hp := μ.val.pos_of_mem_rowLens
  cases he : μ.val.rowLens with
  | nil => simp [he] at hs
  | cons a t =>
    have ha := hp a (by simp [he])
    cases t with
    | nil =>
      have ha2 : a = 2 := by simpa [he] using hs
      left; apply rows_ext; simp [he, ha2]
    | cons b t =>
      have hb := hp b (by simp [he])
      cases t with
      | nil =>
        have ha1 : a = 1 := by simp only [he, List.sum_cons, List.sum_nil] at hs; omega
        have hb1 : b = 1 := by simp only [he, List.sum_cons, List.sum_nil] at hs; omega
        right; apply rows_ext; simp [he, ha1, hb1]
      | cons c t =>
        have hc := hp c (by simp [he])
        simp only [he, List.sum_cons] at hs
        omega

theorem row2_ne_col2 : row2 ≠ col2 := by
  intro he
  have hh := congrArg (fun μ : DegreeShape 2 => μ.val.rowLens) he
  simp at hh

@[simp] theorem h_empty : hPartition emptyShape.val = 1 := by
  simp [hPartition]
@[simp] theorem e_empty : ePartition emptyShape.val = 1 := by
  simp [ePartition]
@[simp] theorem h_row2 : hPartition row2.val = h 2 := by simp [hPartition]
@[simp] theorem h_col2 : hPartition col2.val = h 1 * h 1 := by simp [hPartition]
@[simp] theorem e_row2 : ePartition row2.val = e 2 := by simp [ePartition]

@[simp] theorem e_col2 : ePartition col2.val = h 1 * h 1 := by
  have he : e 1 = h 1 := by
    simp [e, h, CompleteElementary.elementary, CompleteElementary.ekSign,
      CompleteElementary.inverseCoeff, Fin.sum_univ_succ, pow_succ]
  simp [ePartition, he]

theorem h2_h11 : quotientPairing (h 2) (h 1 * h 1) = 1 := by
  have hz := degree_two_eh
  rw [elementary_two] at hz
  simp only [map_sub, LinearMap.sub_apply, degree_two_hh] at hz
  rw [quotientPairing_symm] at hz
  omega

theorem h11_h11 : quotientPairing (h 1 * h 1) (h 1 * h 1) = 0 := by
  have hn := degree_two_ee
  rw [elementary_two] at hn
  simp only [map_sub, LinearMap.sub_apply, degree_two_hh, h2_h11,
    quotientPairing_symm (h 1 * h 1) (h 2)] at hn
  omega

/-- The complete degree2 Gram tables, verified in actual Q. -/
theorem degree_two_gram :
    M 2 row2 row2 = 0 ∧ M 2 row2 col2 = 1 ∧ M 2 col2 row2 = 1 ∧ M 2 col2 col2 = 0 ∧
    Mh 2 row2 row2 = 1 ∧ Mh 2 row2 col2 = 1 ∧ Mh 2 col2 row2 = 1 ∧ Mh 2 col2 col2 = 0 ∧
    Me 2 row2 row2 = -1 ∧ Me 2 row2 col2 = 1 ∧ Me 2 col2 row2 = 1 ∧ Me 2 col2 col2 = 0 := by
  simp [M, Mh, Me, degree_two_eh, degree_two_hh, degree_two_ee, h2_h11, h11_h11,
    elementary_two, quotientPairing_symm (h 1 * h 1) (h 2)]

theorem empty_dual_unit : (mBasis 0 emptyShape : Q) = 1 ∧ (fBasis 0 emptyShape : Q) = 1 := by
  let u : degreePiece 0 := ⟨1, unit_mem_degree_zero⟩
  have hm : u = mBasis 0 emptyShape := m_unique 0 emptyShape u (by
    intro μ; rw [degree_zero_shape μ]; simp [u, empty_pairing])
  have hf : u = fBasis 0 emptyShape := f_unique 0 emptyShape u (by
    intro μ; rw [degree_zero_shape μ]; simp [u, empty_pairing])
  exact ⟨(congrArg Subtype.val hm).symm, (congrArg Subtype.val hf).symm⟩

/-- Hand predictions for BOTH dual bases, not just their norms. -/
theorem degree_two_duals :
    (mBasis 2 row2 : Q) = h 1 * h 1 ∧
    (mBasis 2 col2 : Q) = e 2 ∧
    (fBasis 2 row2 : Q) = h 1 * h 1 ∧
    (fBasis 2 col2 : Q) = h 2 := by
  have hm2 : degreeHBasis 2 col2 = mBasis 2 row2 := m_unique 2 row2 _ (by
    intro μ; rcases degree_two_shapes μ with rfl | rfl <;>
      simp [h2_h11, h11_h11, row2_ne_col2, Ne.symm row2_ne_col2])
  have hm11 : degreeEBasis 2 row2 = mBasis 2 col2 := m_unique 2 col2 _ (by
    intro μ; rcases degree_two_shapes μ with rfl | rfl <;>
      simp [elementary_two, degree_two_hh, h2_h11, h11_h11,
        quotientPairing_symm (h 1 * h 1) (h 2), row2_ne_col2])
  have hf2 : degreeHBasis 2 col2 = fBasis 2 row2 := f_unique 2 row2 _ (by
    intro μ; rcases degree_two_shapes μ with rfl | rfl <;>
      simp [elementary_two, degree_two_hh, h2_h11, h11_h11,
        row2_ne_col2, Ne.symm row2_ne_col2])
  have hf11 : degreeHBasis 2 row2 = fBasis 2 col2 := f_unique 2 col2 _ (by
    intro μ; rcases degree_two_shapes μ with rfl | rfl <;>
      simp [degree_two_eh, quotientPairing_symm (h 1 * h 1) (h 2), h2_h11, row2_ne_col2])
  exact ⟨by simpa using (congrArg Subtype.val hm2).symm,
    by simpa using (congrArg Subtype.val hm11).symm,
    by simpa using (congrArg Subtype.val hf2).symm,
    by simpa using (congrArg Subtype.val hf11).symm⟩

/-- Arbitrary d and arbitrary element: usable integral coordinates and reconstruction. -/
theorem arbitrary_degree_consumer (d : ℕ) (x : degreePiece d) :
    (∀ μ, (mBasis d).repr x μ = quotientPairing (hPartition μ.val) x.val) ∧
    (∀ μ, (fBasis d).repr x μ = quotientPairing (ePartition μ.val) x.val) ∧
    x = ∑ μ, quotientPairing (hPartition μ.val) x.val • mBasis d μ :=
  ⟨m_coordinates d x, f_coordinates d x, reconstruct_m d x⟩

/-- Negative controls: dropping the cable sign gives the wrong norm, and
identifying m₂ with h₂ gives the wrong h₁₁-pairing. -/
theorem cable_sign_required : quotientPairing (e 2) (e 2) ≠ 1 := by
  rw [degree_two_ee]
  norm_num

theorem wrong_m_row2_rejected : (mBasis 2 row2 : Q) ≠ h 2 := by
  intro he
  have hz := h_m 2 col2 row2
  rw [he, h_col2, quotientPairing_symm, h2_h11] at hz
  simp [Ne.symm row2_ne_col2] at hz

theorem southwest_northeast_sign_control :
    EKPairingMatrices.crossing (!![0,1;1,0] : Fin 2 → Fin 2 → ℕ) = 1 ∧
    EKPairingMatrices.crossing (!![1,0;0,1] : Fin 2 → Fin 2 → ℕ) = 0 := by decide

end OddMath.Frontier.EKDualBasesControls

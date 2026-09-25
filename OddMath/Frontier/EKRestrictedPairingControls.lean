import OddMath.Frontier.EKDualBasesControls
import OddMath.Frontier.EKSemiorthogonality

/-! EK Lemma 2.15 controls (compiled BEFORE production).

Hand fixtures: the empty diagram and the two degree-two extremal partitions,
with row-length, cardinality and transpose facts proved explicitly.
Controls reuse only already-compiled pairing values; they assert no new
mathematics. The reversed-cutoff control records the source's own warning:
with `≥` replaced by `≤` the lemma fails, since `(h₁₁, h₁₁) = 0`.
-/
namespace OddMath.Frontier.EKRestrictedPairingControls
open EKSemiorthogonality EKRadicalQuotient EKElementaryQuotient

/-- Hand fixtures: empty diagram and degree-two extremal partitions. -/
def dEmpty : YoungDiagram := YoungDiagram.ofRowLens [] (by decide)
def d2 : YoungDiagram := YoungDiagram.ofRowLens [2] (by decide)
def d11 : YoungDiagram := YoungDiagram.ofRowLens [1,1] (by decide)

@[simp] theorem dEmpty_rows : dEmpty.rowLens = [] := by
  unfold dEmpty
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem d2_rows : d2.rowLens = [2] := by
  unfold d2
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem d11_rows : d11.rowLens = [1,1] := by
  unfold d11
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)

theorem dEmpty_card : dEmpty.card = 0 := by decide
theorem d2_card : d2.card = 2 := by decide
theorem d11_card : d11.card = 2 := by decide

theorem d2_transpose : d2.transpose = d11 := by
  apply YoungDiagram.ext
  decide
theorem d11_transpose : d11.transpose = d2 := by
  apply YoungDiagram.ext
  decide

/-- Empty-degree control: the empty partition word is the unit. -/
theorem empty_word_unit : hPartition dEmpty = 1 := by
  simp [hPartition, dEmpty_rows]

/-- Empty-degree control: unit self-pairing (degree zero is nondegenerate). -/
theorem empty_pairing_unit :
    quotientPairing (hPartition dEmpty) (hPartition dEmpty) = 1 := by
  rw [empty_word_unit]
  exact EKDualBasesControls.empty_pairing

/-- Top-corner control: mixed diagonal at the lex-maximal degree-2 partition. -/
theorem top_corner_nonzero :
    quotientPairing (hPartition d2) (ePartition d11) ≠ 0 := by
  have h := proposition_2_14_diagonal d2
  rw [d2_transpose] at h
  rw [h]
  exact pow_ne_zero _ (by norm_num)

/-- Bottom-corner control: mixed diagonal at the lex-minimal degree-2 partition. -/
theorem bottom_corner_nonzero :
    quotientPairing (hPartition d11) (ePartition d2) ≠ 0 := by
  have h := proposition_2_14_diagonal d11
  rw [d11_transpose] at h
  rw [h]
  exact pow_ne_zero _ (by norm_num)

/-- Reversed-cutoff control (source p.18): `(h₁₁, h₁₁) = 0`, so the lemma
with `≥` replaced by `≤` is already false at degree two. -/
theorem reversed_cutoff_fails :
    quotientPairing (hPartition d11) (hPartition d11) = 0 := by
  have he : hPartition d11 = h 1 * h 1 := by
    simp [hPartition, d11_rows]
  rw [he]
  exact EKDualBasesControls.degree_two_h11_h11

end OddMath.Frontier.EKRestrictedPairingControls

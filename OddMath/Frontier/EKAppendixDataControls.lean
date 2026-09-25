import OddMath.Frontier.EKDualBasesControls
import OddMath.Frontier.TableauDominance

/-! PRE-production controls
(EK1107.5610v2 pp.36-39, Appendix: Data, Secs. 5.1-5.2), compiled BEFORE
`EKAppendixData`. These controls do not use the production evaluator: every
value below comes from existing lemmas proved by a different (algebraic)
route, `EKDualBasesControls.degree_two_gram` and `TableauDominance.signedKostka_diag`.

Hand derivation (independent of production):
* Sec. 5.2, q = -1, degree 2, printed order h11, h2:  [[0,1],[1,1]].
  EK (3.2) matrix formula: (h11,h11) = sum over the two 2x2 permutation matrices
  of (-1)^crossing = 1 + (-1) = 0; (h11,h2) = (h2,h11) = 1 (one matrix);
  (h2,h2) = 1 (one matrix, no crossing).
* Sec. 5.1, degree 2 diagonal: K_{(11),(11)} = K_{(2),(2)} = 1 (normalisation (2.6)).
* Deliberately altered entry: printed (h11,h11) = 0 changed to 1 must FAIL.
  (A second altered-entry control against the production evaluator itself is in
  `EKAppendixDataAudit`; the Python transcription control is
  an unpublished script.)
-/
namespace OddMath.Frontier.EKAppendixDataControls
open EKDualBases EKDualBasesControls TableauDominance

/-- Printed Sec. 5.2 degree-2 q = -1 table in printed order (h11, h2), via the
existing algebraic route (not the production evaluator). -/
theorem printed_quotient_deg2 :
    Mh 2 col2 col2 = 0 ∧ Mh 2 col2 row2 = 1 ∧ Mh 2 row2 col2 = 1 ∧ Mh 2 row2 row2 = 1 := by
  have h := degree_two_gram
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.1⟩

/-- Printed Sec. 5.1 degree-2 diagonal Kostka entries. -/
theorem printed_kostka_deg2_diag :
    signedKostka col2.val col2.val = 1 ∧ signedKostka row2.val row2.val = 1 :=
  ⟨signedKostka_diag _, signedKostka_diag _⟩

/-- Negative control: the deliberately altered entry (h11,h11) := 1 fails. -/
theorem altered_entry_fails : ¬ Mh 2 col2 col2 = 1 := by
  rw [printed_quotient_deg2.1]; decide

end OddMath.Frontier.EKAppendixDataControls

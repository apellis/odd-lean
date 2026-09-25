import OddMath.Frontier.EKRestrictedPairing

/-! Audit of the two proof gaps in EK Lemma 2.15 (1107.5610v2, p.18).

Gap 1 (mod-2 descent): the source concludes `H≥λ ∩ E>λᵀ = {0}` over `ℤ`
from triviality after reduction mod 2, but never proves mod-2 triviality.
`odd_witness_mod_two` shows the obstructing pair of
`EKRestrictedPairing.complement_equality_false` has ODD pairing, so
non-orthogonality survives reduction mod 2: no mod-2 miracle can remove
it. (Separately, a hand partition count at `λ = (3,3)`, degree six, gives
five lex-cutoff `h`-generators at or above `[3,3]` and seven strict
`e`-generators above `[2,2,2]` versus eleven partitions of six; that
informal count is not formalized in this module.)

Gap 2 (determinant-unit step): "nondegenerate on each, `det|H · det|E =
det`, hence each `= ±1`" needs the whole Gram matrix to be block
diagonal in an adapted basis -- i.e. exactly the refuted complement
equality plus exhaustion. `det_unit_step` isolates the only valid
fragment: the arithmetic inference from a unit product to unit factors.
-/
namespace OddMath.Frontier.EKRestrictedPairingAudit
open EKSemiorthogonality EKRadicalQuotient EKRestrictedPairing

/-- The obstructing pairing is odd, hence nonzero mod 2. -/
theorem odd_witness_mod_two :
    (quotientPairing (hPartition mu411) (ePartition nu3111)) % 2 = 1 := by
  have h := proposition_2_14_diagonal mu411
  rw [transpose411] at h
  rw [h]
  rcases Nat.even_or_odd (ell mu411) with he | ho
  · have e1 : (-1 : ℤ) ^ ell mu411 = 1 := he.neg_one_pow
    rw [e1]
    decide
  · have e1 : (-1 : ℤ) ^ ell mu411 = -1 := ho.neg_one_pow
    rw [e1]
    decide

/-- Valid arithmetic fragment of the determinant-unit step: a unit
product of integers forces unit factors. The source applies this to
`det|H · det|E = det = ±1`, whose hypothesis needs the false
block-diagonal premise audited above. -/
theorem det_unit_step (a b : ℤ) (h : a * b = 1 ∨ a * b = -1) :
    (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) := by
  rcases h with h | h
  · exact ⟨Int.isUnit_iff.mp (isUnit_of_mul_eq_one a b h),
      Int.isUnit_iff.mp (isUnit_of_mul_eq_one b a (by rw [mul_comm]; exact h))⟩
  · have ha : IsUnit a :=
      isUnit_of_mul_eq_one a (-b) (by rw [mul_neg, h, neg_neg])
    have h' : b * a = -1 := by rw [mul_comm]; exact h
    have hb : IsUnit b :=
      isUnit_of_mul_eq_one b (-a) (by rw [mul_neg, h', neg_neg])
    exact ⟨Int.isUnit_iff.mp ha, Int.isUnit_iff.mp hb⟩

end OddMath.Frontier.EKRestrictedPairingAudit

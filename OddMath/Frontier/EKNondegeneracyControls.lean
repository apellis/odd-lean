import OddMath.Frontier.EKRestrictedPairingControls

/-! EK Lemma 2.15 restricted-nondegeneracy controls
(compiled BEFORE `EKNondegeneracy`).

Hand fixtures (degree 0 and degree 2) reuse only already-compiled pairing
values of the actual integral quotient `Q` and `quotientPairing`; they assert
no new mathematics.

* empty degree: the unit self-pairing is `1` (degree zero is nondegenerate);
* top extreme cutoff at degree two: `H≥(2) = span{h₂}` and `(h₂,h₂) = 1`;
* literal `(h₁₁,h₁₁) = 0` control: with the reversed cutoff the one-generator
  space `span{h₁₁}` is totally isotropic although `h₁₁ ≠ 0`, so the cutoff
  direction genuinely matters for restricted nondegeneracy.
-/
namespace OddMath.Frontier.EKNondegeneracyControls
open EKSemiorthogonality EKRadicalQuotient EKElementaryQuotient
open EKRestrictedPairingControls

/-- Empty-degree control: degree-zero unit self-pairing. -/
theorem empty_degree :
    quotientPairing (hPartition dEmpty) (hPartition dEmpty) = 1 :=
  empty_pairing_unit

/-- Top extreme cutoff at degree two: the generator `h₂ = h(2)` of `H≥(2)`
pairs to the unit with itself. -/
theorem top_cutoff_unit :
    quotientPairing (hPartition d2) (hPartition d2) = 1 := by
  have he : hPartition d2 = h 2 := by
    simp [hPartition, d2_rows]
  rw [he]
  exact EKDualBasesControls.degree_two_hh

/-- Literal `(h₁₁,h₁₁) = 0` control (source p.18 warning). -/
theorem h11_h11_zero :
    quotientPairing (hPartition d11) (hPartition d11) = 0 :=
  reversed_cutoff_fails

/-- The isotropic generator is a genuine nonzero element of `Q`: its pairing
with `e(2)` is the Proposition 2.14 diagonal value `±1`. -/
theorem h11_ne_zero : hPartition d11 ≠ 0 := by
  intro h0
  have hb := bottom_corner_nonzero
  rw [h0] at hb
  simp at hb

/-- Reversed-cutoff isotropy on the whole one-generator span: every element
`c • h₁₁` pairs to zero with every element `c' • h₁₁`. -/
theorem h11_span_isotropic (c c' : ℤ) :
    quotientPairing (c • hPartition d11) (c' • hPartition d11) = 0 := by
  simp only [map_smul, LinearMap.smul_apply, h11_h11_zero, smul_zero]

end OddMath.Frontier.EKNondegeneracyControls

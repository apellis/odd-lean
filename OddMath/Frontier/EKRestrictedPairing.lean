import OddMath.Frontier.EKTriangular
import OddMath.Frontier.EKSemiorthogonality
import OddMath.Frontier.EKRestrictedPairingControls

/-! EK Lemma 2.15 (1107.5610v2, p.18) restricted-pairing successor.

Source claim: for any partition `λ ⊢ n`, with lexicographic order, the
integral bilinear form is nondegenerate when restricted to `H≥λ` and to
`E>λᵀ`, via `(H≥λ)⊥ = E>λᵀ` inside `Λₙ` and `H≥λ ∩ E>λᵀ = {0}`.

Outcome (obstruction, not proof): the orthogonal-complement equality is
FALSE as stated. At degree six, for `λ = (3,3)` (so `λᵀ = (2,2,2)`), the
element `e(3,1,1,1)` lies in `E>λᵀ` but is NOT orthogonal to `H≥λ`:
its pairing with `h(4,1,1) ∈ H≥λ` is the Proposition 2.14 diagonal value
`±1 ≠ 0`. All objects are the actual integral quotient objects
(`EKSemiorthogonality.hPartition/ePartition`,
`EKRadicalQuotient.quotientPairing`); carriers are unchanged.
The restricted-nondegeneracy conclusions are NOT proved here, and no Gram
determinant computation is evidenced here; they remain OPEN. The only
valid fragment of the source determinant-unit step (a unit product of
integers forces unit factors) is isolated in
`EKRestrictedPairingAudit.det_unit_step`, whose block-diagonal
hypothesis needs the refuted complement equality.
-/
namespace OddMath.Frontier.EKRestrictedPairing
open EKSemiorthogonality EKRadicalQuotient EKTriangular

/-- Source `E_{>λᵀ}`: integral span of the `e`-partition vectors of degree
`d` strictly lexicographically above `λᵀ`. Same module-map carrier
convention as `EKTriangular.Hge`. -/
def Egt (d : ℕ) (lam : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ ν : YoungDiagram,
    ν.card = d ∧ List.Lex (· < ·) lam.transpose.rowLens ν.rowLens ∧
      ePartition ν = x}

/-- Production fixtures: `λ = (3,3)`, `μ = (4,1,1) ∈ H≥λ`,
`ν = (3,1,1,1) = μᵀ ∈ E>λᵀ`, and `λᵀ = (2,2,2)`. -/
def lam33 : YoungDiagram := YoungDiagram.ofRowLens [3,3] (by decide)
def mu411 : YoungDiagram := YoungDiagram.ofRowLens [4,1,1] (by decide)
def nu3111 : YoungDiagram := YoungDiagram.ofRowLens [3,1,1,1] (by decide)
def lamT222 : YoungDiagram := YoungDiagram.ofRowLens [2,2,2] (by decide)

@[simp] theorem lam33_rows : lam33.rowLens = [3,3] := by
  unfold lam33
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem mu411_rows : mu411.rowLens = [4,1,1] := by
  unfold mu411
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem nu3111_rows : nu3111.rowLens = [3,1,1,1] := by
  unfold nu3111
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)
@[simp] theorem lamT222_rows : lamT222.rowLens = [2,2,2] := by
  unfold lamT222
  exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by simp)

theorem lam33_card : lam33.card = 6 := by decide
theorem mu411_card : mu411.card = 6 := by decide
theorem nu3111_card : nu3111.card = 6 := by decide

theorem transpose411 : mu411.transpose = nu3111 := by
  apply YoungDiagram.ext
  decide
theorem transpose33 : lam33.transpose = lamT222 := by
  apply YoungDiagram.ext
  decide

theorem lex33_411 : List.Lex (· < ·) lam33.rowLens mu411.rowLens := by
  rw [lam33_rows, mu411_rows]
  decide
theorem lexT222_3111 :
    List.Lex (· < ·) lam33.transpose.rowLens nu3111.rowLens := by
  rw [transpose33, lamT222_rows, nu3111_rows]
  decide

/-- `h(4,1,1)` lies in `H≥(3,3)`: same degree, lex above. -/
theorem mem_Hge_411 : hPartition mu411 ∈ Hge lam33 := by
  apply Submodule.subset_span
  exact ⟨mu411, by rw [mu411_card, lam33_card], Or.inr lex33_411, rfl⟩

/-- `e(3,1,1,1)` lies in `E>(2,2,2)`: same degree, strictly lex above `λᵀ`. -/
theorem mem_Egt_3111 : ePartition nu3111 ∈ Egt 6 lam33 := by
  apply Submodule.subset_span
  exact ⟨nu3111, nu3111_card, lexT222_3111, rfl⟩

/-- The mixed pairing on the witness pair is the nonzero diagonal value. -/
theorem witness_pairing_nonzero :
    quotientPairing (hPartition mu411) (ePartition nu3111) ≠ 0 := by
  have h := proposition_2_14_diagonal mu411
  rw [transpose411] at h
  rw [h]
  exact pow_ne_zero _ (by norm_num)

/-- Obstruction: the source orthogonal-complement equality
`(H≥λ)⊥ = E>λᵀ` is false. `E>λᵀ` is not even contained in `(H≥λ)⊥`:
the exhibited `y ∈ E>λᵀ` pairs non-trivially with an `x ∈ H≥λ`.
Objects and signs are the actual quotient ones; no carrier is altered. -/
theorem complement_equality_false :
    ∃ y ∈ Egt 6 lam33, ∃ x ∈ Hge lam33,
      quotientPairing x y ≠ 0 :=
  ⟨ePartition nu3111, mem_Egt_3111, hPartition mu411, mem_Hge_411,
    witness_pairing_nonzero⟩

end OddMath.Frontier.EKRestrictedPairing

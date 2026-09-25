import OddMath.Frontier.EKNondegeneracy

/-! EK Lemma 2.15 restricted-nondegeneracy audit (machine-generated).

* Arbitrary-element consumers on the ACTUAL spaces `Hge lam33` (= H≥(3,3))
  and `Egt 6 lam33` (= E>(2,2,2)): restricted nondegeneracy ↔ injectivity of
  the restricted pairing-to-dual map.
* Exact integer identities `GH * NH = 1`, `GE * NE = 1`.
* CONDITIONAL consumers `nondeg_of_GH_table/GE_table` (kept from run 2231).
* UNCONDITIONAL closures (run 2236): `gramH_actual`/`gramE_actual` DERIVE the
  tables from the actual `quotientPairing` (sound evaluator, kernel decide);
  `Hge_le_span`/`Egt_le_span` + `hL_mem`/`eL_mem` prove the actual spaces EQUAL
  the explicit spans (exact source lex, all size-6 Young diagrams);
  `Hge33_nondeg`, `Egt222_nondeg` and the injectivity consumers follow.

Scope: degree 6, `λ = (3,3)` only; no all-λ, no perfectness/surjectivity, no
complement/direct-sum claim.  Row/column order:
`GH`: h(6),h(5,1),h(4,2),h(4,1,1),h(3,3);
`GE`: e(6),e(5,1),e(4,2),e(4,1,1),e(3,3),e(3,2,1),e(3,1,1,1).
-/
namespace OddMath.Frontier.EKNondegeneracyAudit
open EKSemiorthogonality EKRadicalQuotient EKNondegeneracy EKRestrictedPairing EKTriangular

/-- Consumer on the actual `H≥(3,3)`. -/
theorem Hge33_nondeg_iff_injective :
    RestrictedNondeg (Hge lam33) ↔ Function.Injective (restrictedDual (Hge lam33)) :=
  restrictedNondeg_iff_injective _

/-- Consumer on the actual `E>(2,2,2)`. -/
theorem Egt222_nondeg_iff_injective :
    RestrictedNondeg (Egt 6 lam33) ↔ Function.Injective (restrictedDual (Egt 6 lam33)) :=
  restrictedNondeg_iff_injective _

/-- `h`-Gram table (emitted from supporting computation; equality with the actual pairing is `gramH_actual`). -/
def GH : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 1, 1, 1, 1;
    1, 0, 2, 1, 0;
    1, 2, 1, 2, 3;
    1, 1, 2, 1, 2;
    1, 0, 3, 2, 0]

/-- Exact integer inverse of `GH`. -/
def NH : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-1, 4, 1, -1, -2;
    4, -5, -2, 1, 2;
    1, -2, -1, 1, 1;
    -1, 1, 1, -1, 0;
    -2, 2, 1, 0, -1]

/-- `e`-Gram table (emitted from supporting computation; equality with the actual pairing is `gramE_actual`). -/
def GE : Matrix (Fin 7) (Fin 7) ℤ :=
  !![-1, 1, -1, 1, 1, 1, -1;
    1, 0, 2, -1, 0, 1, 0;
    -1, 2, -1, 2, 3, 3, -3;
    1, -1, 2, -1, -2, -2, 1;
    1, 0, 3, -2, 0, 2, 0;
    1, 1, 3, -2, 2, 6, -1;
    -1, 0, -3, 1, 0, -1, 0]

/-- Exact integer inverse of `GE`. -/
def NE : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 3, 0, 0, -1, 0, 1;
    3, 5, -1, -1, 0, -1, 1;
    0, -1, 0, 0, 0, 0, -1;
    0, -1, 0, 1, -2, 1, -1;
    -1, 0, 0, -2, 1, -1, -1;
    0, -1, 0, 1, -1, 1, 0;
    1, 1, -1, -1, -1, 0, -1]

theorem GH_mul_NH : GH * NH = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GH, NH, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem GE_mul_NE : GE * NE = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GE, NE, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Conditional: a family with actual Gram matrix `GH` spans a
restricted-nondegenerate submodule. -/
theorem nondeg_of_GH_table (g : Fin 5 → Q)
    (hg : ∀ i j, quotientPairing (g i) (g j) = GH i j) :
    RestrictedNondeg (Submodule.span ℤ (Set.range g)) := by
  apply nondeg_of_gram_right_inverse g NH
  have hG : (Matrix.of fun i j => quotientPairing (g i) (g j)) = GH := Matrix.ext hg
  rw [hG]
  exact GH_mul_NH

/-- Conditional: a family with actual Gram matrix `GE` spans a
restricted-nondegenerate submodule. -/
theorem nondeg_of_GE_table (g : Fin 7 → Q)
    (hg : ∀ i j, quotientPairing (g i) (g j) = GE i j) :
    RestrictedNondeg (Submodule.span ℤ (Set.range g)) := by
  apply nondeg_of_gram_right_inverse g NE
  have hG : (Matrix.of fun i j => quotientPairing (g i) (g j)) = GE := Matrix.ext hg
  rw [hG]
  exact GE_mul_NE

/-! ### Unconditional closure (run 2236)

The tables are now machine-DERIVED from the actual `quotientPairing` via the
proved-sound evaluator `EKNondegeneracy.pairing_hL/pairing_eL` (kernel
`decide +kernel`), and the actual spaces are proved EQUAL to the spans of the
explicit families by exhaustive exact-lex classification of all size-6 shapes
(`EKNondegeneracy.rowLens_mem_parts`, completeness for every Young diagram). -/

/-- Row lists of the `h`-family (emitted from `SH`). -/
def hRows : Fin 5 → List ℕ := ![[6], [5,1], [4,2], [4,1,1], [3,3]]

/-- Row lists of the `e`-family (emitted from `SE`). -/
def eRows : Fin 7 → List ℕ := ![[6], [5,1], [4,2], [4,1,1], [3,3], [3,2,1], [3,1,1,1]]

/-- Actual Gram matrix of the `h`-family equals `GH` (derived, not assumed). -/
theorem gramH_actual : ∀ i j, quotientPairing (hL (hRows i)) (hL (hRows j)) = GH i j := by
  intro i j; rw [pairing_hL]; revert i j; decide +kernel

/-- Actual Gram matrix of the `e`-family equals `GE` (derived, not assumed). -/
theorem gramE_actual : ∀ i j, quotientPairing (eL (eRows i)) (eL (eRows j)) = GE i j := by
  intro i j; rw [pairing_eL]; revert i j; decide +kernel

/-- Exact-lex classification: every partition of 6 that is `≥ (3,3)` is a listed `h`-row. -/
theorem classifyH : ∀ l ∈ partsF 6 6 6, (l = [3,3] ∨ List.Lex (· < ·) [3,3] l) →
    ∃ i, hRows i = l := by decide

/-- Exact-lex classification: every partition of 6 that is `> (2,2,2)` is a listed `e`-row. -/
theorem classifyE : ∀ l ∈ partsF 6 6 6, List.Lex (· < ·) [2,2,2] l →
    ∃ i, eRows i = l := by decide

theorem hRows_ok : ∀ i, (hRows i).Sorted (· ≥ ·) ∧ (∀ x ∈ hRows i, 0 < x) ∧
    (hRows i).sum = 6 ∧ (hRows i = [3,3] ∨ List.Lex (· < ·) [3,3] (hRows i)) := by decide

theorem eRows_ok : ∀ i, (eRows i).Sorted (· ≥ ·) ∧ (∀ x ∈ eRows i, 0 < x) ∧
    (eRows i).sum = 6 ∧ List.Lex (· < ·) [2,2,2] (eRows i) := by decide

theorem hL_mem (l : List ℕ) (hs : l.Sorted (· ≥ ·)) (hp : ∀ x ∈ l, 0 < x) (hsum : l.sum = 6)
    (hlex : l = [3,3] ∨ List.Lex (· < ·) [3,3] l) : hL l ∈ Hge lam33 := by
  apply Submodule.subset_span
  refine ⟨YoungDiagram.ofRowLens l hs, ?_, ?_, ?_⟩
  · rw [EKPartitionSpanning.card_ofRowLens, hsum, lam33_card]
  · rcases hlex with rfl | h
    · left; rfl
    · right; rw [lam33_rows, YoungDiagram.rowLens_ofRowLens_eq_self hp]; exact h
  · rw [EKPartitionSpanning.hPartition, YoungDiagram.rowLens_ofRowLens_eq_self hp]; rfl

theorem eL_mem (l : List ℕ) (hs : l.Sorted (· ≥ ·)) (hp : ∀ x ∈ l, 0 < x) (hsum : l.sum = 6)
    (hlex : List.Lex (· < ·) [2,2,2] l) : eL l ∈ Egt 6 lam33 := by
  apply Submodule.subset_span
  refine ⟨YoungDiagram.ofRowLens l hs, ?_, ?_, ?_⟩
  · rw [EKPartitionSpanning.card_ofRowLens, hsum]
  · rw [transpose33, lamT222_rows, YoungDiagram.rowLens_ofRowLens_eq_self hp]; exact hlex
  · rw [EKSemiorthogonality.ePartition, YoungDiagram.rowLens_ofRowLens_eq_self hp]; rfl

/-- `H≥(3,3)` is contained in the span of the explicit `h`-family (all shapes). -/
theorem Hge_le_span : Hge lam33 ≤ Submodule.span ℤ (Set.range fun i => hL (hRows i)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨ν, hc, hlex, rfl⟩
  have hm := rowLens_mem_parts 6 ν (by rw [hc, lam33_card])
  obtain ⟨i, hi⟩ := classifyH _ hm (by
    rcases hlex with rfl | h
    · left; exact lam33_rows
    · right; rwa [lam33_rows] at h)
  exact Submodule.subset_span ⟨i, by show _ = _; simp only []; rw [hi]; rfl⟩

/-- `E>(2,2,2)` is contained in the span of the explicit `e`-family (all shapes). -/
theorem Egt_le_span : Egt 6 lam33 ≤ Submodule.span ℤ (Set.range fun i => eL (eRows i)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨ν, hc, hlex, rfl⟩
  have hm := rowLens_mem_parts 6 ν hc
  obtain ⟨i, hi⟩ := classifyE _ hm (by rwa [transpose33, lamT222_rows] at hlex)
  exact Submodule.subset_span ⟨i, by show _ = _; simp only []; rw [hi]; rfl⟩

/-- EK Lemma 2.15 target (i): restricted nondegeneracy of the actual `H≥(3,3)`. -/
theorem Hge33_nondeg : RestrictedNondeg (Hge lam33) := by
  apply nondeg_of_le_span _ (fun i => hL (hRows i)) NH
  · intro i; obtain ⟨a, b, c, d⟩ := hRows_ok i; exact hL_mem _ a b c d
  · exact Hge_le_span
  · have hG : (Matrix.of fun i j => quotientPairing (hL (hRows i)) (hL (hRows j))) = GH :=
      Matrix.ext gramH_actual
    rw [hG]; exact GH_mul_NH

/-- EK Lemma 2.15 target (ii): restricted nondegeneracy of the actual `E>(2,2,2)`. -/
theorem Egt222_nondeg : RestrictedNondeg (Egt 6 lam33) := by
  apply nondeg_of_le_span _ (fun i => eL (eRows i)) NE
  · intro i; obtain ⟨a, b, c, d⟩ := eRows_ok i; exact eL_mem _ a b c d
  · exact Egt_le_span
  · have hG : (Matrix.of fun i j => quotientPairing (eL (eRows i)) (eL (eRows j))) = GE :=
      Matrix.ext gramE_actual
    rw [hG]; exact GE_mul_NE

/-- Injectivity of the restricted pairing-to-dual map on the actual `H≥(3,3)`. -/
theorem Hge33_injective : Function.Injective (restrictedDual (Hge lam33)) :=
  (restrictedNondeg_iff_injective _).mp Hge33_nondeg

/-- Injectivity of the restricted pairing-to-dual map on the actual `E>(2,2,2)`. -/
theorem Egt222_injective : Function.Injective (restrictedDual (Egt 6 lam33)) :=
  (restrictedNondeg_iff_injective _).mp Egt222_nondeg

end OddMath.Frontier.EKNondegeneracyAudit

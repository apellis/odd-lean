import OddMath.Frontier.OddSchurPieri
import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.TableauExtremal

/-! Controls (Ellis 1111.3932v1, Lemma 3.5 and the last paragraph
of the proof of Theorem 3.8).  Compiled BEFORE the production module; imports only inherited
modules.

* Must-hold: unconditional exact sp = schur on the column shapes (1^k) for N = 2 (k ≤ 2) and
  N = 3 (k ≤ 3), and on the empty shape for every N ≥ 2, computed from the inherited literal
  objects (no production lemma, no Pieri hypothesis).  The remaining |λ| ≤ 4, N ≤ 3 grid is
  checked by exact integer arithmetic in an unpublished script.
* Must-fail: the triangular elimination order is lex on the TRANSPOSE λ^T.  On the explicit
  Pieri step λ = (2,1) = β + {row 0}, β = (1,1), k = 1, the other strip term is ν = (1,1,1).
  Column-lex (the printed order) puts ν strictly above λ; the row-lex variant and the
  off-by-one column-index variant (columns 2..r+1 instead of 1..r) both put ν strictly BELOW λ,
  so an induction in either variant order cannot eliminate ν. -/
namespace OddMath.Frontier.OddLREliminationControls
open OddSymmetrizer OddSchurPieri TableauStripSigns
open OddMath.SkewPolynomial (SkewPolynomial)

/-! ## Must-hold: literal column and empty-shape checks -/

theorem north_col2 : north (TableauExtremal.columnShape 2) = 1 := by decide
theorem dnorth_col2 : directNorth (TableauExtremal.columnShape 2) = 1 := by decide
theorem north_col3 : north (TableauExtremal.columnShape 3) = 3 := by decide
theorem dnorth_col3 : directNorth (TableauExtremal.columnShape 3) = 3 := by decide
theorem north_col1 : north (TableauExtremal.columnShape 1) = 0 := by decide
theorem dnorth_col1 : directNorth (TableauExtremal.columnShape 1) = 0 := by decide
theorem north_col0 : north (TableauExtremal.columnShape 0) = 0 := by decide
theorem dnorth_col0 : directNorth (TableauExtremal.columnShape 0) = 0 := by decide

/-- sp on (1^k), from the inherited literal tableau sum, for a given sign exponent. -/
theorem sp_col_of (N k : ℕ) (h : directNorth (TableauExtremal.columnShape k) =
    north (TableauExtremal.columnShape k)) :
    CompleteTableauExpansion.sp N (TableauExtremal.columnShape k) =
      (-1 : ℤ) ^ k.choose 2 • FiniteCompleteElementary.elementaryPoly N k := by
  rw [CompleteTableauExpansion.sp, TableauExtremal.tableauPolynomial_column, h, smul_smul,
    ← pow_add, ← two_mul, pow_add, pow_mul]
  norm_num

/-- Unconditional exact check, N = 3 (n = 1), all columns k ≤ 3. -/
theorem sp_eq_schur_col_N3 :
    CompleteTableauExpansion.sp 3 (TableauExtremal.columnShape 0) = schur 1 (column 1 0) ∧
    CompleteTableauExpansion.sp 3 (TableauExtremal.columnShape 1) = schur 1 (column 1 1) ∧
    CompleteTableauExpansion.sp 3 (TableauExtremal.columnShape 2) = schur 1 (column 1 2) ∧
    CompleteTableauExpansion.sp 3 (TableauExtremal.columnShape 3) = schur 1 (column 1 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [schur_column _ _ (by norm_num), sp_col_of]
  · rw [dnorth_col0, north_col0]
  · rw [dnorth_col1, north_col1]
  · rw [dnorth_col2, north_col2]
  · rw [dnorth_col3, north_col3]

/-- Unconditional exact check, N = 2 (n = 0), all columns k ≤ 2. -/
theorem sp_eq_schur_col_N2 :
    CompleteTableauExpansion.sp 2 (TableauExtremal.columnShape 0) = schur 0 (column 0 0) ∧
    CompleteTableauExpansion.sp 2 (TableauExtremal.columnShape 1) = schur 0 (column 0 1) ∧
    CompleteTableauExpansion.sp 2 (TableauExtremal.columnShape 2) = schur 0 (column 0 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  rw [schur_column _ _ (by norm_num), sp_col_of]
  · rw [dnorth_col0, north_col0]
  · rw [dnorth_col1, north_col1]
  · rw [dnorth_col2, north_col2]

/-- Nondegeneracy of the column check: the N = 3, k = 3 value is not zero-by-accident
of the sign; both sides equal the signed literal e_3 with sign (-1)^3 = -1. -/
theorem col3_sign : ((-1 : ℤ) ^ (3 : ℕ).choose 2) = -1 := by decide

/-! ## Lex-order controls on an explicit Pieri step -/

/-- Column length of a row-length vector (local copy; production defines its own). -/
def colLenC {N : ℕ} (α : Fin N → ℕ) (j : ℕ) : ℕ := (Finset.univ.filter (fun i => j < α i)).card

def lamC : Fin 3 → ℕ := ![2, 1, 0]
def betaC : Fin 3 → ℕ := ![1, 1, 0]
def nuC : Fin 3 → ℕ := ![1, 1, 1]

/-- Both strip terms of β = (1,1) with k = 1 that are partitions: λ (row 0) and ν (row 2). -/
theorem strip_terms :
    increment betaC {0} = lamC ∧ increment betaC {2} = nuC ∧
    Antitone lamC ∧ Antitone nuC ∧ ¬ Antitone (increment betaC {1}) ∧ nuC ≠ lamC := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- λ is β plus the removed last column (width r = 2, c = colLen λ 1 = 1). -/
theorem lam_decomp : colLenC lamC 1 = 1 ∧ (fun i => min (lamC i) (lamC 0 - 1)) = betaC := by
  refine ⟨by decide, by decide⟩

/-- Printed order (lex on λ^T, columns 1..r): ν is strictly above λ.  Must hold. -/
theorem column_lex_holds :
    toLex (fun j : Fin 2 => colLenC lamC j) < toLex (fun j : Fin 2 => colLenC nuC j) :=
  ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by decide⟩

/-- Variant 1 (row lex instead of transpose lex): ν is strictly BELOW λ, so the claim
"every other strip term is lex-greater" FAILS in this order. -/
theorem row_lex_variant_fails : ¬ (toLex lamC < toLex nuC) := by
  have h : toLex nuC < toLex lamC := ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by decide⟩
  exact fun h' => lt_asymm h h'

/-- Variant 2 (off-by-one column index: columns 2..r+1): ν is strictly BELOW λ, FAILS. -/
theorem shifted_column_variant_fails :
    ¬ (toLex (fun j : Fin 2 => colLenC lamC (j.val+1)) <
      toLex (fun j : Fin 2 => colLenC nuC (j.val+1))) := by
  have h : toLex (fun j : Fin 2 => colLenC nuC (j.val+1)) <
      toLex (fun j : Fin 2 => colLenC lamC (j.val+1)) :=
    ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by decide⟩
  exact fun h' => lt_asymm h h'

end OddMath.Frontier.OddLREliminationControls

import OddMath.Frontier.EKDualBasesControls
import OddMath.Frontier.CompleteTableauExpansion

/-! PRE-production controls for EK1107.5610v2 Thm 3.7 (3.9), compiled BEFORE
`EKKostkaValues`. Hand derivation (independent of production):

* d = 2, order (2),(1,1): Mh = [[1,1],[1,0]] (EK (3.2) M′, printed p24);
  signedKostka rows λ, cols μ: [[1,1],[0,1]].
  RHS entry (μ,ρ) = Σ_λ (-1)^(λ₂+λ₄+…) K_{λμ} K_{λρ}:
    ((2),(2))   = (+1)·1·1 + (-1)·0·0 = 1,
    ((2),(11))  = (+1)·1·1 + (-1)·0·1 = 1,
    ((11),(11)) = (+1)·1·1 + (-1)·1·1 = 0.   Matches Mh.
* Exponent convention: Σ_j C(λᵀ_j,2) = Σ_i (i)·λ_{i+1} (0-based) ≡ λ₂+λ₄+… mod 2.
  λ=(2,2): Σ C(λᵀ,2) = 1+1 = 2, λ₂ = 2 → sign +1.
  λ=(1,1,1,1): C(4,2) = 6, λ₂+λ₄ = 2 → sign +1; but the WRONG row-binomial
  Σ C(λ_i,2) = 0 and the WRONG odd-row sum λ₁+λ₃ = 2 agree here, whereas
  λ=(1,1,1): C(3,2) = 3 (odd), λ₂ = 1 (odd), WRONG λ₁+λ₃ = 2 (even).
  The existing statistic used in production is `TableauStripSigns.directNorth`
  = #{(q,p) cells : q strictly north of p in the same column} = Σ_j C(λᵀ_j,2).
Exact values below are machine-checked from the existing definitions. -/
namespace OddMath.Frontier.EKKostkaValuesControls
open TableauStripSigns EKDualBases EKDualBasesControls

def dg (w : List ℕ) (hw : w.Sorted (· ≥ ·)) : YoungDiagram := YoungDiagram.ofRowLens w hw

/-- λ=(2,2): directNorth = Σ_j C(λᵀ_j,2) = 2. -/
theorem directNorth_22 : directNorth (dg [2,2] (by decide)) = 2 := by decide
/-- λ=(1,1,1,1): directNorth = C(4,2) = 6 (even, like λ₂+λ₄ = 2). -/
theorem directNorth_1111 : directNorth (dg [1,1,1,1] (by decide)) = 6 := by decide
/-- λ=(1,1,1): directNorth = 3 (odd, like λ₂ = 1; unlike λ₁+λ₃ = 2). -/
theorem directNorth_111 : directNorth (dg [1,1,1] (by decide)) = 3 := by decide
theorem directNorth_2 : directNorth (dg [2] (by decide)) = 0 := by decide
theorem directNorth_11 : directNorth (dg [1,1] (by decide)) = 1 := by decide
theorem directNorth_211 : directNorth (dg [2,1,1] (by decide)) = 3 := by decide
theorem directNorth_321 : directNorth (dg [3,2,1] (by decide)) = 4 := by decide

/-- Degree-two M′ = Mh table, from the actual quotient pairing. -/
theorem mh_degree_two :
    Mh 2 row2 row2 = 1 ∧ Mh 2 row2 col2 = 1 ∧ Mh 2 col2 row2 = 1 ∧ Mh 2 col2 col2 = 0 := by
  have h := degree_two_gram
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem kostka_diag_degree_two :
    TableauDominance.signedKostka row2.val row2.val = 1 ∧
    TableauDominance.signedKostka col2.val col2.val = 1 :=
  ⟨TableauDominance.signedKostka_diag _, TableauDominance.signedKostka_diag _⟩

end OddMath.Frontier.EKKostkaValuesControls

import OddMath.Frontier.EKFinalRibbonDet
import OddMath.Frontier.EKFinalPrinted

/-!
# Block-diagonalised determinant certificates for the ribbon Gram matrix

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, pp. 39–40.

The ribbon Gram matrix `G̃ = ((h̃_β, h̃_α))` of (2.33) is invariant under reversal of
compositions (`σ ↦ w₀σw₀` preserves length and reverses descent sets).  For an integer matrix
`T` whose columns are the vectors `e_α ± e_{α^rev}`, the matrix `Tᵀ G̃ T` is block diagonal.
This file proves, for an arbitrary integer matrix `T` (given by its rows `Tr` and by the rows
`Tc` of its transpose, related only through the checked product `Tc · Tr`):

* `det_of_symCert`: if `Tc · Tr` is upper triangular with diagonal product `c ≠ 0` and the certificate
  `certCheck` shows `det (Tc · G · Tr) = c · v`, then `det G = v`.
* `gram_det_eq_of_symCheck`: the resulting certified identity `det G_n(q) = Q(q)` in `ℤ[q]`
  (Kronecker substitution at `q = 2^K` with the a priori bound of `EKFinalRibbonDet`).

The multiplier matrix of the certificate may be computed blockwise; only the product is checked.
`revTc`, `revTr`, `blockL` give the reversal change of basis and the blockwise multipliers.
No instance of `symCheck` is evaluated in this file.
-/

noncomputable section
open Polynomial

namespace OddMath.Frontier.EKFinal
open EKGeneralQ EKRest

theorem det_of_symCert (N : ℕ) (G Tc Tr L : List (List ℤ)) (c v : ℤ)
    (hG : shapeOK N G = true) (hTc : shapeOK N Tc = true) (hTr : shapeOK N Tr = true)
    (hP2 : upperOK N (mulLL N Tc Tr) = true)
    (hc : diagProd N (mulLL N Tc Tr) = c) (hc0 : c ≠ 0)
    (hcert : certCheck N (mulLL N Tc (mulLL N G Tr)) L (c * v) = true) :
    (ofLL N G).det = v := by
  have h1 := det_of_cert N _ L _ hcert
  rw [ofLL_mulLL N Tc _ hTc (shapeOK_mulLL N G Tr hG), ofLL_mulLL N G Tr hG hTr,
    Matrix.det_mul, Matrix.det_mul] at h1
  have hP : (ofLL N Tc).det * (ofLL N Tr).det = c := by
    rw [← Matrix.det_mul, ← ofLL_mulLL N Tc Tr hTc hTr, det_ofLL_upper hP2, hc]
  have : (ofLL N G).det * c = v * c := by
    rw [← hP]
    linear_combination h1 - v * hP
  exact mul_right_cancel₀ hc0 this

/-- The combined check for degree `n` with a change of basis `T` (rows `Tr`, transpose rows
`Tc`) and a certificate generator `Lgen`. -/
def symCheck (n K : ℕ) (fs : List (List ℤ × ℕ)) (Tc Tr : List (List ℤ))
    (Lgen : List (List ℤ) → List (List ℤ)) (c : ℤ) : Bool :=
  shapeOK (2 ^ (n - 1)) (ribbonLL n K) && shapeOK (2 ^ (n - 1)) Tc &&
    shapeOK (2 ^ (n - 1)) Tr &&
    upperOK (2 ^ (n - 1)) (mulLL (2 ^ (n - 1)) Tc Tr) &&
    diagProd (2 ^ (n - 1)) (mulLL (2 ^ (n - 1)) Tc Tr) == c && !(c == 0) &&
    certCheck (2 ^ (n - 1)) (mulLL (2 ^ (n - 1)) Tc (mulLL (2 ^ (n - 1)) (ribbonLL n K) Tr))
      (Lgen (mulLL (2 ^ (n - 1)) Tc (mulLL (2 ^ (n - 1)) (ribbonLL n K) Tr)))
      (c * prodPowEval (2 ^ K) fs) &&
    decide (2 * (colBound (2 ^ (n - 1)) (ribbonLL n 0) + prodPowEval 1 (absFs fs)) < 2 ^ K)

/-- **Certified Gram determinant** via a block-diagonalising change of basis. -/
theorem gram_det_eq_of_symCheck {n : ℕ} (hn : 0 < n) (K : ℕ) (fs : List (List ℤ × ℕ))
    (Tc Tr : List (List ℤ)) (Lgen : List (List ℤ) → List (List ℤ)) (c : ℤ)
    (h : symCheck n K fs Tc Tr Lgen c = true) : (gram (X : ℤ[X]) n).det = prodPow fs := by
  simp only [symCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hG, hTc⟩, hTr⟩, hP2⟩, hc⟩, hc0⟩, hcert⟩, hb⟩ := h
  apply eq_of_eval_of_bound _ _ (2 ^ K) _ (prodPowEval 1 (absFs fs))
    (abs_coeff_gram_det_le_ribbon hn)
  · intro e
    have := (maj_prodPow fs).le_eval_one e
    rwa [eval_prodPow] at this
  · exact hb
  · rw [eval_gram_det, det_gram_eq_gramHt _ hn, det_gramHt_ribbon,
      det_of_symCert _ _ _ _ _ _ _ hG hTc hTr hP2 hc hc0 hcert, eval_prodPow]

/-! ## The reversal change of basis -/

/-- Reversal of the `m` low bits (acting on binary masks of cut sets). -/
def revBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | m + 1, i, acc => revBits m (i / 2) (2 * acc + i % 2)

/-- Columns `e_i + e_{ρi}` (`i ≤ ρi`), then `e_i - e_{ρi}` (`i < ρi`), for `ρ` the reversal
of `m`-bit masks, in `ℤ^{2^m}`. -/
def revCols (m : ℕ) : List (ℕ × ℕ × ℤ) :=
  ((List.range (2 ^ m)).filter (fun i => i ≤ revBits m i 0)).map (fun i => (i, revBits m i 0, 1)) ++
  ((List.range (2 ^ m)).filter (fun i => i < revBits m i 0)).map (fun i => (i, revBits m i 0, -1))

def colVec (N : ℕ) (c : ℕ × ℕ × ℤ) : List ℤ :=
  (List.range N).map fun a =>
    (if a = c.1 then 1 else 0) + (if a = c.2.1 ∧ c.2.1 ≠ c.1 then c.2.2 else 0)

/-- Rows of `Tᵀ`. -/
def revTc (m : ℕ) : List (List ℤ) := (revCols m).map (colVec (2 ^ m))

/-- Rows of `T`. -/
def revTr (m : ℕ) : List (List ℤ) :=
  (List.range (2 ^ m)).map fun a => (revTc m).map fun col => col.getD a 0

/-- The principal submatrix on rows/columns `a, …, a + b - 1`. -/
def subLL (M : List (List ℤ)) (a b : ℕ) : List (List ℤ) :=
  ((M.drop a).take b).map fun r => (r.drop a).take b

/-- Blockwise fraction-free elimination: multipliers for the two diagonal blocks of sizes
`s₁`, `s₂`. -/
def blockL (s₁ s₂ : ℕ) (M : List (List ℤ)) : List (List ℤ) :=
  (bareissL s₁ (subLL M 0 s₁)).map (fun r => r ++ List.replicate s₂ 0) ++
  (bareissL s₂ (subLL M s₁ s₂)).map (fun r => List.replicate s₁ 0 ++ r)

end OddMath.Frontier.EKFinal

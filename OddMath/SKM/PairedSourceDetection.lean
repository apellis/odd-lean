import OddMath.SKM.PairedSourceCupColumns
import OddMath.SKM.OrientedReduction

/-! Finite detection by the all-height paired source columns. The
proof uses greatest isolated-cap dot count, not a global grading bound. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (B : SameColourSourceFrame P Q Z i)
  (cs : CScalars Sc) (μ : X)

/-- Read the low cup pivot or the shifted principal pivot. -/
def sourceNegativeEntry (N : ℕ) (row col : B.residual.Labels × ℕ) (d : SYM D k) : SYM D k :=
  if row.2 < N then
    B.sourceCupColumn cs μ N col.2 (N - 1 - row.2) col.1 row.1 * SYM.parityTwist D k (((N - 1 - row.2 : ℕ) : ZMod 2) * D.parity i) d
  else B.sourceNegativeColumn cs μ N col.2 col.1 (row.1, row.2 - N) * SYM.parityTwist D k (D.parity i) d

private theorem sourceNegativeEntry_below (N : ℕ) (row col : B.residual.Labels × ℕ)
    (d : SYM D k) (h : col.2 < row.2) :
    B.sourceNegativeEntry cs μ N row col d = 0 := by
  classical
  rw [sourceNegativeEntry]
  split_ifs with hr
  · rw [B.sourceCupColumn_below cs μ N row.2 col.2 col.1 hr h]
    simp
  · by_cases hc : col.2 < N
    · simp [sourceNegativeColumn, hc]
    · rw [B.sourceNegativeColumn_above cs μ N col.2 (row.2 - N)
        col.1 row.1 (by omega) (by omega)]
      have hn : (col.1, col.2 - N) ≠ (row.1, row.2 - N) := by
        intro he
        have := congrArg Prod.snd he
        omega
      simp [hn]

private theorem sourceNegativeEntry_same (N : ℕ) (row col : B.residual.Labels × ℕ)
    (d : SYM D k) (h : col.2 = row.2) (hn : col ≠ row) :
    B.sourceNegativeEntry cs μ N row col d = 0 := by
  classical
  have hl : col.1 ≠ row.1 := by
    intro he
    exact hn (Prod.ext he h)
  rw [sourceNegativeEntry]
  split_ifs with hr
  · rw [h, B.sourceCupColumn_pivot cs μ N row.2 col.1 hr]
    simp [hl]
  · rw [B.sourceNegativeColumn_above cs μ N col.2 (row.2 - N)
      col.1 row.1 (by omega) (by omega)]
    simp [hl]

private theorem sourceNegativeEntry_detects (N : ℕ) (row : B.residual.Labels × ℕ)
    (d : SYM D k) (h : B.sourceNegativeEntry cs μ N row row d = 0) : d = 0 := by
  classical
  unfold sourceNegativeEntry at h
  split_ifs at h with hr
  · rw [B.sourceCupColumn_pivot cs μ N row.2 row.1 hr] at h
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_mul_assoc, one_mul] at h
    have hz := (cs.c (wt D μ Q) i)⁻¹.isUnit.smul_eq_zero.mp h
    have H := congrArg (SYM.parityTwist D k (((N - 1 - row.2 : ℕ) : ZMod 2) * D.parity i)) hz
    simpa only [SYM.parityTwist_involutive, map_zero] using H
  · rw [B.sourceNegativeColumn_above cs μ N row.2 (row.2 - N)
      row.1 row.1 (by omega) le_rfl] at h
    simp only [Finsupp.single_eq_same, smul_mul_assoc, one_mul] at h
    have hz := (paired_source_pivot_isUnit cs i (wt D μ Q) (row.2 - N)).smul_eq_zero.mp h
    have H := congrArg (SYM.parityTwist D k (D.parity i)) hz
    simpa only [SYM.parityTwist_involutive, map_zero] using H

/-- Vanishing of the low-cup and shifted principal pivot coefficients
forces a finite paired coefficient family to vanish. No residual or source
independence assumption is hidden in this coefficient statement. -/
theorem sourceNegativeColumns_detect (N : ℕ) (f : (B.residual.Labels × ℕ) →₀ SYM D k)
    (h : ∀ row, (∑ col ∈ f.support,
      B.sourceNegativeEntry cs μ N row col (f col)) = 0) : f = 0 := by
  apply OrientedReduction.eq_zero_of_crossing_dot_coefficients
    Prod.snd (fun _ => 0) (B.sourceNegativeEntry cs μ N)
    (B.sourceNegativeEntry_below cs μ N)
    (fun _ _ _ _ h => by omega)
    (fun row col d he _ hn => B.sourceNegativeEntry_same cs μ N row col d he hn)
    (B.sourceNegativeEntry_detects cs μ N) f h

/-- At nonnegative height the shifted principal rows alone detect all paired
coefficients. The missing initial rows are not required. -/
theorem sourceNonnegativeColumns_detect (N : ℕ) (f : (B.residual.Labels × ℕ) →₀ SYM D k)
    (h : ∀ row : B.residual.Labels × ℕ, (∑ col ∈ f.support,
      B.sourceNonnegativeColumn cs μ N col.2 col.1 (row.1, row.2 + N) * SYM.parityTwist D k (D.parity i) (f col)) = 0) :
    f = 0 := by
  classical
  refine OrientedReduction.eq_zero_of_crossing_dot_coefficients
    Prod.snd (fun _ => 0)
    (fun row col d => B.sourceNonnegativeColumn cs μ N col.2 col.1
      (row.1, row.2 + N) * SYM.parityTwist D k (D.parity i) d) ?_ (fun _ _ _ _ h => by omega) ?_ ?_ f h
  · intro row col d hc
    rw [B.sourceNonnegativeColumn_above cs μ N col.2 (row.2 + N)
      col.1 row.1 (by omega)]
    have hn : (col.1, col.2 + N) ≠ (row.1, row.2 + N) := by
      intro he
      have := congrArg Prod.snd he
      omega
    simp [hn]
  · intro row col d hc _ hn
    rw [B.sourceNonnegativeColumn_above cs μ N col.2 (row.2 + N)
      col.1 row.1 (by omega)]
    have hl : col.1 ≠ row.1 := by
      intro he
      exact hn (Prod.ext he hc)
    simp [hl]
  · intro row d hd
    rw [B.sourceNonnegativeColumn_above cs μ N row.2 (row.2 + N)
      row.1 row.1 le_rfl] at hd
    simp only [Finsupp.single_eq_same, smul_mul_assoc, one_mul] at hd
    have hz := (paired_source_initial_pivot_isUnit cs i (wt D μ Q) row.2).smul_eq_zero.mp hd
    have H := congrArg (SYM.parityTwist D k (D.parity i)) hz
    simpa only [SYM.parityTwist_involutive, map_zero] using H

end SameColourSourceFrame
end OddMath.SKM

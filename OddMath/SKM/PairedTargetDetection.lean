import OddMath.SKM.PairedTargetCapColumns
import OddMath.SKM.OrientedReduction

/-! Finite detection by the actual all-height paired target columns. The
proof uses greatest isolated-cup dot count, not a global grading bound. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace MatchingBasisChoice
variable {a P Q : List (Letter I)} (B : MatchingBasisChoice a (P ++ Q))
  (cs : CScalars Sc) (μ : X) (i : I)

/-- Read the low cap pivot or the shifted principal pivot. -/
def targetPositiveEntry (N : ℕ) (row col : B.Labels × ℕ) (d : SYM D k) : SYM D k :=
  if row.2 < N then
    B.targetCapColumn cs μ i N col.2 (N - 1 - row.2) col.1 row.1 * d
  else B.targetPositiveColumn cs μ i N col.2 col.1 (row.1, row.2 - N) * d

private theorem targetPositiveEntry_below (N : ℕ) (row col : B.Labels × ℕ)
    (d : SYM D k) (h : col.2 < row.2) :
    B.targetPositiveEntry cs μ i N row col d = 0 := by
  classical
  rw [targetPositiveEntry]
  split_ifs with hr
  · rw [B.targetCapColumn_below cs μ i N row.2 col.2 col.1 hr h]
    simp
  · by_cases hc : col.2 < N
    · simp [targetPositiveColumn, hc]
    · rw [B.targetPositiveColumn_above cs μ i N col.2 (row.2 - N)
        col.1 row.1 (by omega) (by omega)]
      have hn : (col.1, col.2 - N) ≠ (row.1, row.2 - N) := by
        intro he
        have := congrArg Prod.snd he
        omega
      simp [hn]

private theorem targetPositiveEntry_same (N : ℕ) (row col : B.Labels × ℕ)
    (d : SYM D k) (h : col.2 = row.2) (hn : col ≠ row) :
    B.targetPositiveEntry cs μ i N row col d = 0 := by
  classical
  have hl : col.1 ≠ row.1 := by
    intro he
    exact hn (Prod.ext he h)
  rw [targetPositiveEntry]
  split_ifs with hr
  · rw [h, B.targetCapColumn_pivot cs μ i N row.2 col.1 hr]
    simp [hl]
  · rw [B.targetPositiveColumn_above cs μ i N col.2 (row.2 - N)
      col.1 row.1 (by omega) (by omega)]
    simp [hl]

private theorem targetPositiveEntry_detects (N : ℕ) (row : B.Labels × ℕ)
    (d : SYM D k) (h : B.targetPositiveEntry cs μ i N row row d = 0) : d = 0 := by
  classical
  unfold targetPositiveEntry at h
  split_ifs at h with hr
  · rw [B.targetCapColumn_pivot cs μ i N row.2 row.1 hr] at h
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_mul_assoc, one_mul] at h
    exact (cs.c (wt D μ Q) i).isUnit.smul_eq_zero.mp h
  · rw [B.targetPositiveColumn_above cs μ i N row.2 (row.2 - N)
      row.1 row.1 (by omega) le_rfl] at h
    simp only [Finsupp.single_eq_same, smul_mul_assoc, one_mul] at h
    exact (paired_target_pivot_isUnit cs i (wt D μ Q) (row.2 - N)).smul_eq_zero.mp h

/-- Vanishing of the actual low-cap and shifted principal pivot coefficients
forces a finite paired coefficient family to vanish. No residual or target
independence assumption is hidden in this coefficient statement. -/
theorem targetPositiveColumns_detect (N : ℕ) (f : (B.Labels × ℕ) →₀ SYM D k)
    (h : ∀ row, (∑ col ∈ f.support,
      B.targetPositiveEntry cs μ i N row col (f col)) = 0) : f = 0 := by
  apply OrientedReduction.eq_zero_of_crossing_dot_coefficients
    Prod.snd (fun _ => 0) (B.targetPositiveEntry cs μ i N)
    (B.targetPositiveEntry_below cs μ i N)
    (fun _ _ _ _ h => by omega)
    (fun row col d he _ hn => B.targetPositiveEntry_same cs μ i N row col d he hn)
    (B.targetPositiveEntry_detects cs μ i N) f h

/-- At nonpositive height the shifted principal rows alone detect all paired
coefficients. The missing initial rows are not required. -/
theorem targetNonpositiveColumns_detect (N : ℕ) (f : (B.Labels × ℕ) →₀ SYM D k)
    (h : ∀ row : B.Labels × ℕ, (∑ col ∈ f.support,
      B.targetNonpositiveColumn cs μ i N col.2 col.1 (row.1, N + row.2) * f col) = 0) :
    f = 0 := by
  classical
  refine OrientedReduction.eq_zero_of_crossing_dot_coefficients
    Prod.snd (fun _ => 0)
    (fun row col d => B.targetNonpositiveColumn cs μ i N col.2 col.1
      (row.1, N + row.2) * d) ?_ (fun _ _ _ _ h => by omega) ?_ ?_ f h
  · intro row col d hc
    rw [B.targetNonpositiveColumn_above cs μ i N col.2 (N + row.2)
      col.1 row.1 (by omega)]
    have hn : (col.1, N + col.2) ≠ (row.1, N + row.2) := by
      intro he
      have := congrArg Prod.snd he
      omega
    simp [hn]
  · intro row col d hc _ hn
    rw [B.targetNonpositiveColumn_above cs μ i N col.2 (N + row.2)
      col.1 row.1 (by omega)]
    have hl : col.1 ≠ row.1 := by
      intro he
      exact hn (Prod.ext he hc)
    simp [hl]
  · intro row d hd
    rw [B.targetNonpositiveColumn_above cs μ i N row.2 (N + row.2)
      row.1 row.1 le_rfl] at hd
    simp only [Finsupp.single_eq_same, smul_mul_assoc, one_mul] at hd
    exact (paired_target_initial_pivot_isUnit cs i (wt D μ Q) row.2).smul_eq_zero.mp hd

end MatchingBasisChoice
end OddMath.SKM

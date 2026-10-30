/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSIterates
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorCoefficients

/-!
# Support of the independent output square product

The degree bound is for the independently defined S of
`DeformedBoundaryDivision.md` §5, not the reverse QP numerator.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed degree of the square-difference product. This is a bound
also on zero old corners; it is not a claim about `natDegree`. -/
def outputSDegree (i : I) (v : List I) : ℕ :=
  (if D.parity i = 1 then 4 else 2) * v.count i

theorem sourceMovingDegree_le_outputSDegree (i : I) (v : List I)
    (a : ℕ) (c : MoveChoices v) :
    sourceMovingDegree (leadingSourceDots D i 0 a v c) ≤ outputSDegree D i v := by
  induction v generalizing a with
  | nil => simp [leadingSourceDots, sourceMovingDegree, outputSDegree]
  | cons j v ih =>
    rcases c with ⟨b, c⟩
    have h := ih (a + 1) c
    change sourceMovingDegree (leadingSourceBlockDots D i j 0 (a + 1) b ++
      leadingSourceDots D i 0 (a + 1) v c) ≤ _
    rw [sourceMovingDegree_append]
    by_cases hij : i = j
    · subst j
      by_cases hi : D.parity i = 1
      all_goals fin_cases b <;>
        simp [leadingSourceBlockDots, sourceMovingDegree, outputSDegree, hi] at h ⊢ <;>
        omega
    · simpa [leadingSourceBlockDots, hij, sourceMovingDegree, outputSDegree,
        Ne.symm hij] using h

/-- The choice of the highest moving term in every local factor. -/
def outputSTopChoice : (v : List I) → MoveChoices v
  | [] => ()
  | _ :: v => (0, outputSTopChoice v)

theorem outputSTopChoice_data (i : I) (v : List I) (a : ℕ) :
    sourceMovingDegree (leadingSourceDots D i 0 a v (outputSTopChoice v)) =
        outputSDegree D i v ∧
    sourceOldDots (leadingSourceDots D i 0 a v (outputSTopChoice v)) = [] ∧
    leadingMoveCoeff D (k := k) i v (outputSTopChoice v) =
        SKM.zsign k (D.parity i) ^ v.count i := by
  induction v generalizing a with
  | nil => simp [leadingSourceDots, sourceMovingDegree,
      sourceOldDots, outputSDegree, leadingMoveCoeff]
  | cons j v ih =>
    have h := ih (a + 1)
    by_cases hij : i = j
    · subst j
      by_cases hi : D.parity i = 1
      all_goals simp [outputSTopChoice, leadingSourceDots, leadingSourceBlockDots,
        sourceMovingDegree, sourceOldDots, leadingMoveCoeff, leadingBlockCoeff,
        outputSDegree, hi, SKM.zsign, pow_succ, h.1, h.2.1, h.2.2,
        mul_comm, Nat.add_comm]; omega
    · simpa [outputSTopChoice, leadingSourceDots, leadingSourceBlockDots,
        sourceMovingDegree, sourceOldDots, leadingMoveCoeff, leadingBlockCoeff,
        outputSDegree, hij, Ne.symm hij] using h

theorem outputSTopChoice_unique (i : I) (v : List I) (a : ℕ) (c : MoveChoices v)
    (hc : leadingMoveCoeff D (k := k) i v c ≠ 0)
    (hd : sourceMovingDegree (leadingSourceDots D i 0 a v c) = outputSDegree D i v) :
    c = outputSTopChoice v := by
  induction v generalizing a with
  | nil => exact @Subsingleton.elim Unit _ _ _
  | cons j v ih =>
    rcases c with ⟨b, c⟩
    change leadingBlockCoeff D i j b * leadingMoveCoeff D i v c ≠ 0 at hc
    have ht : leadingMoveCoeff D (k := k) i v c ≠ 0 := by
      intro hz
      exact hc (by rw [hz, mul_zero])
    have hb := sourceMovingDegree_le_outputSDegree D i v (a + 1) c
    change sourceMovingDegree (leadingSourceBlockDots D i j 0 (a + 1) b ++
      leadingSourceDots D i 0 (a + 1) v c) = _ at hd
    rw [sourceMovingDegree_append] at hd
    have hzero : b = 0 := by
      by_cases hij : i = j
      · subst j
        by_cases hi : D.parity i = 1
        all_goals fin_cases b <;>
          simp [leadingSourceBlockDots, sourceMovingDegree, outputSDegree, hi] at hd hb ⊢ <;>
          omega
      · by_contra h
        exact hc (by simp [leadingBlockCoeff, hij, h])
    subst b
    have htail : sourceMovingDegree (leadingSourceDots D i 0 (a + 1) v c) =
        outputSDegree D i v := by
      by_cases hij : i = j
      · subst j
        by_cases hi : D.parity i = 1
        all_goals
          simp [leadingSourceBlockDots, sourceMovingDegree, outputSDegree, hi] at hd ⊢
          omega
      · simpa [leadingSourceBlockDots, hij, sourceMovingDegree, outputSDegree,
          Ne.symm hij] using hd
    change (0, c) = (0, outputSTopChoice v)
    rw [ih (a + 1) c ht htail]

namespace ELVOld

theorem independentOutputS_above (i : I) (v : List I) (n : ℕ)
    (hn : outputSDegree D i v < n) : independentOutputS D Sc cutoff i v n = 0 := by
  rw [independentOutputS_apply]
  have h : (∑ c : MoveChoices v,
      if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
        leadingMoveCoeff D (k := k) i v c •
          (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [ite_eq_right]
    have hc := sourceMovingDegree_le_outputSDegree D i v 0 c
    omega
  rw [h, smul_zero]

theorem independentOutputS_top (i : I) (v : List I) :
    independentOutputS D Sc cutoff i v (outputSDegree D i v) =
      (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  rw [independentOutputS_apply, Finset.sum_eq_single (outputSTopChoice v)]
  · have h := outputSTopChoice_data D (k := k) i v 0
    rw [h.1, ite_eq_left rfl, h.2.2, smul_smul]
    have hs : (SKM.zsign k (D.parity i) ^ v.count i) *
        (SKM.zsign k (D.parity i) ^ v.count i) = 1 := by
      rw [← mul_pow]
      by_cases hi : D.parity i = 1 <;> simp [SKM.zsign, hi]
    rw [hs, one_smul]
    congr 1
    unfold leadingSourceOldArrow
    rw [h.2.1]
    unfold endpointDotMonomial
    simp only [List.map_nil, cl_nil D Sc v rfl, affineUnit_id]
  · intro c _ hc
    split_ifs with hd
    · have hz : leadingMoveCoeff D (k := k) i v c = 0 := by
        by_contra hz
        exact hc (outputSTopChoice_unique D i v 0 c hz hd)
      rw [hz, zero_smul]
    · rfl
  · simp

theorem independentOutputS_support (i : I) (v : List I) :
    (independentOutputS D Sc cutoff i v).support ⊆
      Finset.range (outputSDegree D i v + 1) := by
  intro n hn
  rw [Finset.mem_range]
  by_contra h
  exact (Finsupp.mem_support_iff.mp hn)
    (independentOutputS_above D Sc cutoff i v n (by omega))

end ELVOld
end OddMath.QuiverHecke

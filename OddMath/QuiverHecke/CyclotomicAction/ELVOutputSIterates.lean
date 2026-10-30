/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputCompatibleLifts
import OddMath.QuiverHecke.CyclotomicAction.ELVReverseBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryFirstOrder
/-!
# Corrected rho iterates of the independent output polynomial

`outputLongExtraction_boundaryRho_move_independentS` identifies every corrected
source iterate with the finite sum of the prescribed corrected long coordinates.
The coefficients are the independently defined ordered square product, not an
extraction-defined polynomial. Their even support and total-twist invariance are
proved before using the corrected even/odd lift formulas.

`reverseBoundary_sub_correctedS_mem` couples this extraction to the ordered
reverse-QP P-image modulo the chronological crossing image. This is the input
from `DeformedBoundaryDivision.md` §4 for the augmented boundary matrix; it does
not assume or construct C₀, S-division, or a matrix inverse. The global library
sign is retained, rather than replaced by the source-convention sign.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem independentOutputS_oldTwist (i : I) (v : List I) (n : ℕ) (q : ZMod 2) :
    oldTwist D Sc cutoff q v v (independentOutputS D Sc cutoff i v n) =
      independentOutputS D Sc cutoff i v n := by
  rw [independentOutputS_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [map_smul]
    congr 1
    change (ideal D Sc cutoff v v).mkQ (twist k q _) = _
    rw [leadingSourceOldArrow_twist]
  · exact map_zero _

theorem independentOutputS_support_even (i : I) (hi : D.parity i = 1)
    (v : List I) {n : ℕ} (hn : n ∈ (independentOutputS D Sc cutoff i v).support) :
    Even n := by
  by_contra he
  have hz : independentOutputS D Sc cutoff i v n = 0 := by
    rw [independentOutputS_apply]
    have hsum : (∑ c : MoveChoices v,
        if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
          leadingMoveCoeff D (k := k) i v c •
            (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [ite_eq_right]
      intro h
      apply he
      rw [← h]
      exact Nat.even_iff.mpr (sourceMovingDegree_leadingSourceDots_even D i hi 0 v c)
    rw [hsum, smul_zero]
  exact (Finsupp.mem_support_iff.mp hn) hz

theorem outputLongExtraction_boundaryRho_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d] z) =
      (outputCoefficientRho D Sc cutoff p j v)^[d]
        (outputLongExtraction D Sc cutoff p j.1 v z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', outputLongExtraction_boundaryRho, ih,
      Function.iterate_succ_apply']

theorem outputCoefficientRho_iterate_even_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ) (hn : Even n)
    (b : Old D Sc cutoff v v) :
    (outputCoefficientRho D Sc cutoff p j v)^[n] (Finsupp.single 0 b) =
      Finsupp.single n b := by
  obtain ⟨q, hq⟩ := hn
  have h : n = 2 * q := by omega
  rw [h]
  rw [← outputLongExtraction_correctedLift, outputCorrectedLift_even,
    outputLongExtraction_lift]

theorem outputCoefficientRho_iterate_independentS (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    (outputCoefficientRho D Sc cutoff p j v)^[d] (independentOutputS D Sc cutoff j.1 v) =
      ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
        outputLongExtraction D Sc cutoff p j.1 v
          (outputCorrectedLift D Sc cutoff p j v (d + n)
            (independentOutputS D Sc cutoff j.1 v n)) := by
  conv_lhs => rw [← Finsupp.sum_single (independentOutputS D Sc cutoff j.1 v)]
  rw [← Module.End.coe_pow]
  change (outputCoefficientRho D Sc cutoff p j v ^ d)
    (∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
      Finsupp.single n (independentOutputS D Sc cutoff j.1 v n)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Module.End.pow_apply, outputLongExtraction_correctedLift,
    Function.iterate_add_apply,
    outputCoefficientRho_iterate_even_single D Sc cutoff p j v n
      (independentOutputS_support_even D Sc cutoff j.1 j.2 v hn)]

theorem outputLongExtraction_boundaryRho_move_independentS (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff (j.1 :: v) (v ++ [j.1]) (moveHom D Sc j.1 [] v)))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (independentOutputS D Sc cutoff j.1 v n)) := by
  rw [outputLongExtraction_boundaryRho_iterate, outputLongExtraction_move_independentS,
    ← Module.End.coe_pow, map_smul, Module.End.pow_apply,
    outputCoefficientRho_iterate_independentS]

theorem outputLongExtraction_boundaryRho_move_even (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (q : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[2 * q]
        (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          Finsupp.single (2 * q + n) (independentOutputS D Sc cutoff j.1 v n) := by
  rw [show move D Sc cutoff j.1 v =
    affineUnit D Sc cutoff (j.1 :: v) (v ++ [j.1]) (moveHom D Sc j.1 [] v) from rfl,
    outputLongExtraction_boundaryRho_move_independentS]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨a, ha⟩ := independentOutputS_support_even D Sc cutoff j.1 j.2 v hn
  have h : 2 * q + n = 2 * (q + a) := by omega
  rw [h, outputCorrectedLift_even, outputLongExtraction_lift]

theorem outputLongExtraction_boundaryRho_move_odd (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (q : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[2 * q + 1]
        (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          (Finsupp.single (2 * q + n + 1) (independentOutputS D Sc cutoff j.1 v n) +
            Finsupp.single (2 * q + n) (outputDeltaCoefficient D Sc cutoff p j v
              (independentOutputS D Sc cutoff j.1 v n))) := by
  rw [show move D Sc cutoff j.1 v =
    affineUnit D Sc cutoff (j.1 :: v) (v ++ [j.1]) (moveHom D Sc j.1 [] v) from rfl,
    outputLongExtraction_boundaryRho_move_independentS]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨a, ha⟩ := independentOutputS_support_even D Sc cutoff j.1 j.2 v hn
  have h : 2 * q + n = 2 * (q + a) := by omega
  have h' : 2 * q + 1 + n = 2 * (q + a) + 1 := by omega
  rw [h', outputCorrectedLift_odd, map_add, outputLongExtraction_lift,
    outputLongExtraction_lift, independentOutputS_oldTwist, h]

/-- The reverse polynomial and the prescribed corrected-basis P-images agree
modulo the chronological crossing image. No polynomial projection is assumed. -/
theorem reverseBoundary_sub_correctedS_mem (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendProjection D Sc cutoff j.1 v (v ++ [j.1])
        (appendMovingPower D Sc cutoff j.1 v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
          endpointELV D Sc cutoff j.1 v) -
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          pMap D Sc cutoff j.1 v (v ++ [j.1])
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (independentOutputS D Sc cutoff j.1 v n)) ∈
        chronologicalCrossingSpan D Sc cutoff j.1 v v := by
  have h := pMap_sub_outputLiftBoundary_mem D Sc cutoff p j v
    ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
      (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v)))
  have hp := pMap_boundaryRho_move_iterate D Sc cutoff j v (v ++ [j.1]) d (𝟙 _)
  simp only [Category.comp_id] at hp
  rw [hp] at h
  change _ - outputLiftBoundary D Sc cutoff p j v
    (outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff _ _ (moveHom D Sc j.1 [] v))))) ∈ _ at h
  rw [outputLongExtraction_boundaryRho_move_independentS, map_smul, map_sum] at h
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  change _ = pMap D Sc cutoff j.1 v (v ++ [j.1])
    (outputLongSection D Sc cutoff p j.1 v
      (outputLongExtraction D Sc cutoff p j.1 v
        (outputCorrectedLift D Sc cutoff p j v (d + n) _)))
  rw [outputLongExtraction_correctedLift, outputLongSection_rho_iterate]


/-- Every balanced right coefficient is retained in chronological old composition;
its total twist remains inside the prescribed corrected lift. -/
theorem outputLongExtraction_boundaryRho_move_balanced (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (b : Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (balancedForward D Sc cutoff p j.1 v (v ++ [j.1])
          (balancedTmul D Sc cutoff p j.1 (move D Sc cutoff j.1 v) b))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (oldComp D Sc cutoff v v v b (independentOutputS D Sc cutoff j.1 v n))) := by
  have hb : outputLongExtraction D Sc cutoff p j.1 v
      (balancedForward D Sc cutoff p j.1 v (v ++ [j.1])
        (balancedTmul D Sc cutoff p j.1 (move D Sc cutoff j.1 v) b)) =
      Finsupp.mapRange.linearMap (oldComp D Sc cutoff v v v b)
        (SKM.zsign k (D.parity j.1) ^ v.count j.1 • independentOutputS D Sc cutoff j.1 v) := by
    ext n
    rw [outputLongExtraction_apply]
    exact outputLongCoordinate_move_independentS_balanced D Sc cutoff p j.1 v b n
  rw [outputLongExtraction_boundaryRho_iterate, hb, map_smul,
    ← Module.End.coe_pow, map_smul]
  congr 1
  conv_lhs => rw [← Finsupp.sum_single (independentOutputS D Sc cutoff j.1 v)]
  change (outputCoefficientRho D Sc cutoff p j v ^ d)
    (Finsupp.mapRange.linearMap (oldComp D Sc cutoff v v v b)
      (∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
        Finsupp.single n (independentOutputS D Sc cutoff j.1 v n))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  rw [Module.End.pow_apply, outputLongExtraction_correctedLift,
    Function.iterate_add_apply,
    outputCoefficientRho_iterate_even_single D Sc cutoff p j v n
      (independentOutputS_support_even D Sc cutoff j.1 j.2 v hn)]

end OddMath.QuiverHecke.ELVOld

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorLeading

/-!
# Ordered division of the actual boundary numerator by independent S

The quotient is the actual boundary of the corrected source vector. The
remainder is computed by the genuine input-dot defect, not chosen by a
polynomial division interface. This is `DeformedBoundaryDivision.md` (9)–(11)
in the input-oriented full-ELV convention.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem oldTwist_add_apply (a b : ZMod 2) (v : List I)
    (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff a v v (oldTwist D Sc cutoff b v v c) =
      oldTwist D Sc cutoff (a + b) v v c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k a (twist k b c)) = _
  rw [← twist_add]
  rfl

private theorem oldTwist_zero_apply (v : List I) (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff 0 v v c = c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
  rw [twist_zero]

private theorem appendInputShift_apply_succ (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ) :
    appendInputShift D Sc cutoff i v v f (m + 1) = oldTwist D Sc cutoff (D.parity i) v v (f m) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single n b =>
    simp only [appendInputShift, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply]
    by_cases h : m = n
    · subst m; simp only [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne h, map_zero]

/-- Exact high-coordinate telescoping of the actual input defect. -/
theorem outputPolynomialBoundary_iterate_high (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      ((outputCoefficientRho D Sc cutoff p j v)^[n] f) (n + m) =
    oldTwist D Sc cutoff (n • D.parity j.1) v v
      (outputPolynomialBoundary D Sc cutoff p j v f m) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add, zero_smul, oldTwist_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', outputPolynomialBoundary_rho]
    have he : n + 1 + m = (n + m) + 1 := by omega
    rw [he, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), add_zero,
      appendInputShift_apply_succ, ih, oldTwist_add_apply]
    congr 2
    simp only [add_smul, one_smul, add_comm]

/-- Chronological right multiplication by the independently defined S.
Input shifts retain the entire-coefficient twist; on S support they are even. -/
def independentSRightProduct (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
    (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff i v n))).comp (inputCoefficientShift D Sc cutoff i v n)

/-- The literal S evaluation, retaining the existing corrected coefficient operator. -/
def independentSAtRho (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
    (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff j.1 v n))).comp
        ((outputCoefficientRho D Sc cutoff p j v) ^ n)

/-- The actual boundary remainder, before normalization by scalar units. -/
def independentSBoundaryRemainder (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) : ℕ →₀ Old D Sc cutoff v v :=
  outputPolynomialBoundary D Sc cutoff p j v (independentSAtRho D Sc cutoff p j v f) -
    independentSRightProduct D Sc cutoff j.1 v (outputPolynomialBoundary D Sc cutoff p j v f)

theorem independentSBoundaryRemainder_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ) (hm : outputSDegree D j.1 v ≤ m) :
    independentSBoundaryRemainder D Sc cutoff p j v f m = 0 := by
  unfold independentSBoundaryRemainder independentSAtRho independentSRightProduct
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply, map_sum,
    outputPolynomialBoundary_independentS_postcomp, Finsupp.sub_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have h := independentOutputS_support D Sc cutoff j.1 v hn
    rw [Finset.mem_range] at h
    omega
  have he : m = n + (m - n) := by omega
  rw [he]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, LinearMap.flip_apply]
  rw [outputPolynomialBoundary_iterate_high, inputCoefficientShift_apply_add]

theorem independentSRightProduct_high (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ)
    (hm : outputSDegree D j.1 v ≤ m) :
    independentSRightProduct D Sc cutoff j.1 v f m =
      ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
        oldComp D Sc cutoff v v v (f (m - n)) (independentOutputS D Sc cutoff j.1 v n) := by
  simp only [independentSRightProduct, LinearMap.sum_apply, LinearMap.comp_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have h := independentOutputS_support D Sc cutoff j.1 v hn
    rw [Finset.mem_range] at h
    omega
  have he : m = n + (m - n) := by omega
  rw [he, inputCoefficientShift_apply_add]
  obtain ⟨q, hq⟩ := independentOutputS_support_even D Sc cutoff j.1 j.2 v hn
  have hp : n • D.parity j.1 = 0 := by
    rw [hq, add_smul, j.2]
    simp only [nsmul_eq_mul, mul_one]
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  rw [hp, oldTwist_zero_apply]
  simp only [Nat.add_sub_cancel_left]

/-- The leading coefficient of the actual S product is the input coefficient,
with no nonzero-corner hypothesis. -/
theorem independentSRightProduct_top (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (M : ℕ)
    (hf : ∀ m, M < m → f m = 0) :
    independentSRightProduct D Sc cutoff j.1 v f (M + outputSDegree D j.1 v) = f M := by
  rw [independentSRightProduct_high D Sc cutoff j v f _ (by omega)]
  rw [Finset.sum_eq_single (outputSDegree D j.1 v)]
  · rw [Nat.add_sub_cancel, independentOutputS_top]
    obtain ⟨b, hb⟩ := (ideal D Sc cutoff v v).mkQ_surjective (f M)
    rw [← hb, oldComp_mk, Category.comp_id]
  · intro n hn hne
    have h := independentOutputS_support D Sc cutoff j.1 v hn
    rw [Finset.mem_range] at h
    rw [hf _ (by omega), map_zero, LinearMap.zero_apply]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- If the S product vanishes above B, each possible input coefficient above
B-D vanishes, phrased without truncated subtraction or a nonzero hypothesis. -/
theorem independentSRightProduct_detect_bound (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (B : ℕ)
    (hf : ∀ m, outputSDegree D j.1 v ≤ m → B < m →
      independentSRightProduct D Sc cutoff j.1 v f m = 0)
    (m : ℕ) (hm : B < m + outputSDegree D j.1 v) : f m = 0 := by
  by_contra h
  have hs : f.support.Nonempty := ⟨m, Finsupp.mem_support_iff.mpr h⟩
  obtain ⟨M, hM, hmax⟩ := f.support.exists_max_image id hs
  have hbound : ∀ n, M < n → f n = 0 := by
    intro n hn
    by_contra hz
    have hh := hmax n (Finsupp.mem_support_iff.mpr hz)
    change n ≤ M at hh
    omega
  have hle := hmax m (Finsupp.mem_support_iff.mpr h)
  change m ≤ M at hle
  have ht := independentSRightProduct_top D Sc cutoff j v f M hbound
  rw [hf _ (by omega) (by omega)] at ht
  exact (Finsupp.mem_support_iff.mp hM) ht.symm

/-- The prescribed boundary value on the corrected source basis. -/
def outputBoundaryPhi (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (d : ℕ) : ℕ →₀ Old D Sc cutoff v v :=
  outputPolynomialBoundary D Sc cutoff p j v
    (outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))

/-- Genuine ordered S quotient/remainder identity for the checked reverse
numerator. The quotient is the actual boundary phi, up to the library sign;
the displayed remainder has support strictly below the independently proved S
bound. No degree-height monicity is assumed. -/
theorem independentS_boundary_division (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    let w := outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))
    let sigma := SKM.zsign k (D.parity j.1) ^ v.count j.1
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      inputCoefficientShift D Sc cutoff j.1 v d
        (orderedQPOutputCoefficients D Sc cutoff j.1 v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff j.1 v)) =
      independentSRightProduct D Sc cutoff j.1 v (sigma • outputBoundaryPhi D Sc cutoff p j v d) +
        sigma • independentSBoundaryRemainder D Sc cutoff p j v w := by
  dsimp only
  rw [map_smul]
  have h := outputPolynomialBoundary_independentS_coefficients D Sc cutoff p j v d
  rw [← h, ← smul_add]
  congr 1
  unfold outputBoundaryPhi independentSBoundaryRemainder independentSAtRho
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply]
  abel

/-- High coefficients of the genuine quotient product equal the signed
reverse numerator exactly. -/
theorem independentS_boundary_division_high (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d m : ℕ)
    (hm : outputSDegree D j.1 v ≤ m) :
    independentSRightProduct D Sc cutoff j.1 v
      (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d) m =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      inputCoefficientShift D Sc cutoff j.1 v d
        (orderedQPOutputCoefficients D Sc cutoff j.1 v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff j.1 v)) m := by
  have h := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f m)
    (independentS_boundary_division D Sc cutoff p j v d)
  simp only [Finsupp.add_apply, Finsupp.smul_apply] at h
  rw [independentSBoundaryRemainder_above D Sc cutoff p j v _ m hm, smul_zero, add_zero] at h
  exact h.symm

/-- The actual boundary quotient has no coefficient beyond the signed
height range. This formulation also covers the negative-height case. -/
theorem outputBoundaryPhi_signed_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d m : ℕ)
    (hm : d + endpointQPDegree D cutoff j.1 v < m + outputSDegree D j.1 v) :
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d) m = 0 := by
  apply independentSRightProduct_detect_bound D Sc cutoff j v _
    (d + endpointQPDegree D cutoff j.1 v) _ m hm
  intro n hn hN
  rw [independentS_boundary_division_high D Sc cutoff p j v d n hn]
  rw [inputCoefficientShift_above D Sc cutoff j.1 v d (endpointQPDegree D cutoff j.1 v) n _
    (orderedReverseNumerator_above D Sc cutoff j.1 v) hN, smul_zero]

/-- In the nonnegative-height range the actual quotient has the prescribed
scalar unit times identity at its leading bound, including zero old corners. -/
theorem outputBoundaryPhi_signed_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (hd : outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) :
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d)
      (d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      ((appendQPProductUnit D Sc j.1 v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) := by
  have ht := independentSRightProduct_top D Sc cutoff j v
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d)
    (d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v)
    (fun m hm => outputBoundaryPhi_signed_above D Sc cutoff p j v d m (by omega))
  have he : d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v +
      outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v := by omega
  rw [he, independentS_boundary_division_high D Sc cutoff p j v d _ hd,
    inputCoefficientShift_unit_top D Sc cutoff j.1 v d _ _ _
      (orderedReverseNumerator_top D Sc cutoff j.1 v)] at ht
  exact ht.symm

end OddMath.QuiverHecke.ELVOld

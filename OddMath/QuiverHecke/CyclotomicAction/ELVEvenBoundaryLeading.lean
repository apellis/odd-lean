/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorLeading
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSLeading

/-! # Coefficients of the even-moving polynomial boundary

Coefficient transport retains the global normalization twist even when the
moving colour is even. All old coefficients remain in the full ELV quotient.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem twistZero (v : List I) (b : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff 0 v v b = b := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
  rw [twist_zero]

private theorem compIdLeft (v : List I) (b : Old D Sc cutoff v v) :
    oldComp D Sc cutoff v v v ((ideal D Sc cutoff v v).mkQ (𝟙 _)) b = b := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  rw [oldComp_mk, Category.id_comp]

private theorem compIdRight (v : List I) (b : Old D Sc cutoff v v) :
    oldComp D Sc cutoff v v v b ((ideal D Sc cutoff v v).mkQ (𝟙 _)) = b := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  rw [oldComp_mk, Category.comp_id]

/-- The identity-coefficient value of the section-defined row. -/
def evenBoundaryPhi (p : ZMod 2) (i : I) (v : List I) (d : ℕ) : ℕ →₀ Old D Sc cutoff v v :=
  evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))

/-- The entire old coefficient is twisted by p; even moving parity does not
remove this normalization. Composition is in chronological order. -/
theorem evenPolynomialBoundary_single_apply (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d n : ℕ) (b : Old D Sc cutoff v v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) n =
      oldComp D Sc cutoff v v v (evenBoundaryPhi D Sc cutoff p i v d n)
        (oldTwist D Sc cutoff p v v b) := by
  have h := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f n)
    (evenPolynomialBoundary_rightAction_even D Sc cutoff p i hi v
      (oldTwist D Sc cutoff p v v b) (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))
  simp only [outputCoefficientRightAction_single, hi, nsmul_zero, add_zero,
    oldTwist_twice, compIdLeft, outputCoefficientRightAction_apply, twistZero] at h
  exact h

private theorem shift_single (v : List I) (m : ℕ) (b : Old D Sc cutoff v v) :
    appendOutputShift D Sc cutoff v v (Finsupp.single m b) = Finsupp.single (m + 1) b := by
  simp only [appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply]

private theorem shift_iterate_single (v : List I) (d m : ℕ) (b : Old D Sc cutoff v v) :
    (appendOutputShift D Sc cutoff v v)^[d] (Finsupp.single m b) = Finsupp.single (d + m) b := by
  induction d with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add]
  | succ d ih => rw [Function.iterate_succ_apply', ih, shift_single]; congr 1; omega

/-- Every positive-coordinate recurrence is the iterate of the actual C₀P
recurrence, not an assumed triangular row property. -/
theorem evenPolynomialBoundary_iterate_high (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ) (f : ℕ →₀ Old D Sc cutoff v v) :
    evenPolynomialBoundary D Sc cutoff p i v ((appendOutputShift D Sc cutoff v v)^[d] f) (d + m) =
      evenPolynomialBoundary D Sc cutoff p i v f m := by
  induction d with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add]
  | succ d ih =>
    rw [Function.iterate_succ_apply', show d + 1 + m = (d + m) + 1 by omega,
      evenPolynomialBoundary_shift_high D Sc cutoff p i hi, ih]

private theorem extraction_iterate (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongExtraction D Sc cutoff p i v
      ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d] z) =
    (appendOutputShift D Sc cutoff v v)^[d] (outputLongExtraction D Sc cutoff p i v z) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', outputLongExtraction_evenDot D Sc cutoff p i hi,
      ih, Function.iterate_succ_apply']

/-- Explicit S-weighted single-coefficient evaluation of the actual boundary
is the ordered reverse numerator for every exponent. -/
theorem evenPolynomialBoundary_shiftedS (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) :
    (∑ n ∈ (independentOutputS D Sc cutoff i v).support,
      evenPolynomialBoundary D Sc cutoff p i v
        (Finsupp.single (d + n) (independentOutputS D Sc cutoff i v n))) =
    inputCoefficientShift D Sc cutoff i v d
      (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
        (endpointOutputCoefficients D Sc cutoff i v)) := by
  have h := evenPolynomialBoundary_reverseNumerator D Sc cutoff p i hi v d
  rw [extraction_iterate D Sc cutoff p i hi] at h
  have hs := outputLongExtraction_move_independentS D Sc cutoff p i v
  simp only [hi, SKM.zsign, zero_ne_one, ↓reduceIte, one_pow, one_smul] at hs
  change outputLongExtraction D Sc cutoff p i v
    (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)) = _ at hs
  rw [hs] at h
  rw [← Finsupp.sum_single (independentOutputS D Sc cutoff i v)] at h
  change evenPolynomialBoundary D Sc cutoff p i v
    ((appendOutputShift D Sc cutoff v v)^[d]
      (∑ n ∈ (independentOutputS D Sc cutoff i v).support,
        Finsupp.single n (independentOutputS D Sc cutoff i v n))) = _ at h
  rw [← Module.End.coe_pow] at h
  rw [map_sum, map_sum] at h
  simp only [Module.End.pow_apply, shift_iterate_single] at h
  exact h

/-- High coefficients of the genuine boundary satisfy ordered convolution
with S. The identity comes from the reverse diagram and C₀'s constant defect. -/
theorem evenBoundaryPhi_convolution (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ) (hm : outputSDegree D i v ≤ m) :
    (∑ n ∈ (independentOutputS D Sc cutoff i v).support,
      oldComp D Sc cutoff v v v (evenBoundaryPhi D Sc cutoff p i v d (m - n))
        (independentOutputS D Sc cutoff i v n)) =
    inputCoefficientShift D Sc cutoff i v d
      (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
        (endpointOutputCoefficients D Sc cutoff i v)) m := by
  have h := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f m)
    (evenPolynomialBoundary_shiftedS D Sc cutoff p i hi v d)
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have hh := independentOutputS_support D Sc cutoff i v hn
    rw [Finset.mem_range] at hh
    omega
  rw [evenPolynomialBoundary_single_apply D Sc cutoff p i hi, independentOutputS_oldTwist]
  congr 1
  unfold evenBoundaryPhi
  rw [show d + n = n + d by omega, ← shift_iterate_single D Sc cutoff v n d]
  rw [show m = n + (m - n) by omega,
    evenPolynomialBoundary_iterate_high D Sc cutoff p i hi]
  simp only [Nat.add_sub_cancel_left]

private theorem convolution_top (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (M : ℕ) (hf : ∀ m, M < m → f m = 0) :
    (∑ n ∈ (independentOutputS D Sc cutoff i v).support,
      oldComp D Sc cutoff v v v (f (M + outputSDegree D i v - n))
        (independentOutputS D Sc cutoff i v n)) = f M := by
  rw [Finset.sum_eq_single (outputSDegree D i v)]
  · rw [Nat.add_sub_cancel, independentOutputS_top, compIdRight]
  · intro n hn hne
    have h := independentOutputS_support D Sc cutoff i v hn
    rw [Finset.mem_range] at h
    rw [hf _ (by omega), map_zero, LinearMap.zero_apply]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- The genuine boundary has no coefficient above the integer-height bound.
The inequality formulation also treats negative height and zero old corners. -/
theorem evenBoundaryPhi_above (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ)
    (hm : d + endpointQPDegree D cutoff i v < m + outputSDegree D i v) :
    evenBoundaryPhi D Sc cutoff p i v d m = 0 := by
  let f := evenBoundaryPhi D Sc cutoff p i v d
  change f m = 0
  by_contra h
  have hs : f.support.Nonempty := ⟨m, Finsupp.mem_support_iff.mpr h⟩
  obtain ⟨M, hM, hmax⟩ := f.support.exists_max_image id hs
  have hb : ∀ n, M < n → f n = 0 := by
    intro n hn
    by_contra hz
    have hh := hmax n (Finsupp.mem_support_iff.mpr hz)
    change n ≤ M at hh
    omega
  have hle := hmax m (Finsupp.mem_support_iff.mpr h)
  change m ≤ M at hle
  have ht := convolution_top D Sc cutoff i v f M hb
  have hc := evenBoundaryPhi_convolution D Sc cutoff p i hi v d
    (M + outputSDegree D i v) (by omega)
  rw [inputCoefficientShift_above D Sc cutoff i v d (endpointQPDegree D cutoff i v) _ _
    (orderedReverseNumerator_above D Sc cutoff i v) (by omega)] at hc
  exact (Finsupp.mem_support_iff.mp hM) (ht.symm.trans hc)

/-- The top coefficient comes from the ordered numerator's explicit scalar
unit. This is an equality at the bound, not a nonzero or natDegree assertion. -/
theorem evenBoundaryPhi_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) (hd : outputSDegree D i v ≤ d + endpointQPDegree D cutoff i v) :
    evenBoundaryPhi D Sc cutoff p i v d
      (d + endpointQPDegree D cutoff i v - outputSDegree D i v) =
    (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have ht := convolution_top D Sc cutoff i v (evenBoundaryPhi D Sc cutoff p i v d)
    (d + endpointQPDegree D cutoff i v - outputSDegree D i v)
    (fun m hm => evenBoundaryPhi_above D Sc cutoff p i hi v d m (by omega))
  have he : d + endpointQPDegree D cutoff i v - outputSDegree D i v + outputSDegree D i v =
      d + endpointQPDegree D cutoff i v := by omega
  rw [he, evenBoundaryPhi_convolution D Sc cutoff p i hi v d _ hd,
    inputCoefficientShift_unit_top D Sc cutoff i v d _ _ _
      (orderedReverseNumerator_top D Sc cutoff i v)] at ht
  exact ht.symm

/-- Full-coefficient support of the actual row on the normalized long basis. -/
theorem evenPolynomialBoundary_single_above (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ) (b : Old D Sc cutoff v v)
    (hm : d + endpointQPDegree D cutoff i v < m + outputSDegree D i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) m = 0 := by
  rw [evenPolynomialBoundary_single_apply D Sc cutoff p i hi,
    evenBoundaryPhi_above D Sc cutoff p i hi v d m hm, map_zero, LinearMap.zero_apply]

/-- Explicit unit times the total old normalization twist, for every old
coefficient, every p, and arbitrary mixed old colours. -/
theorem evenPolynomialBoundary_single_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) (b : Old D Sc cutoff v v)
    (hd : outputSDegree D i v ≤ d + endpointQPDegree D cutoff i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b)
      (d + endpointQPDegree D cutoff i v - outputSDegree D i v) =
      (appendQPProductUnit D Sc i v : k) • oldTwist D Sc cutoff p v v b := by
  rw [evenPolynomialBoundary_single_apply D Sc cutoff p i hi,
    evenBoundaryPhi_top D Sc cutoff p i hi v d hd, map_smul, LinearMap.smul_apply, compIdLeft]

/-- Below the height threshold the whole boundary value is zero. -/
theorem evenPolynomialBoundary_single_eq_zero (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) (b : Old D Sc cutoff v v)
    (hd : d + endpointQPDegree D cutoff i v < outputSDegree D i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) = 0 := by
  ext m
  exact evenPolynomialBoundary_single_above D Sc cutoff p i hi v d m b (by omega)

/-- The explicit leading coefficient map is an equivalence even on an
annihilated old corner: scalar-unit multiplication after the total p twist. -/
def evenBoundaryLeadingEquiv (p : ZMod 2) (i : I) (v : List I) :
    Old D Sc cutoff v v ≃ₗ[k] Old D Sc cutoff v v :=
  (LinearEquiv.ofInvolutive (oldTwist D Sc cutoff p v v)
    (oldTwist_twice D Sc cutoff p v v)).trans
      (LinearEquiv.smulOfUnit (appendQPProductUnit D Sc i v))

/-- The invertible coefficient map is the actual coefficient at its signed
height, with the index stated without truncated subtraction. -/
theorem evenPolynomialBoundary_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d n : ℕ) (b : Old D Sc cutoff v v)
    (hn : n + outputSDegree D i v = d + endpointQPDegree D cutoff i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) n =
      evenBoundaryLeadingEquiv D Sc cutoff p i v b := by
  have he : n = d + endpointQPDegree D cutoff i v - outputSDegree D i v := by omega
  rw [he, evenPolynomialBoundary_single_top D Sc cutoff p i hi v d b (by omega)]
  rfl

end OddMath.QuiverHecke.ELVOld

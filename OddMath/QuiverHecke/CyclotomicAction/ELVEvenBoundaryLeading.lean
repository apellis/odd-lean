import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenSRightProduct
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorLeading

/-! # Leading coefficients of the even polynomial boundary

The parity-zero independent-S argument in DeformedBoundaryDivision (5).
The boundary is the specified arbitrary-Hom C0P map. Its diagonal row on the
old identity has the prescribed scalar-unit top coefficient and vanishes
above its bound, including the negative-height case and zero old corners.
This is a diagonal coefficient theorem, not an even categorical inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The canonical diagonal specialization retains full coefficient covariance. -/
theorem offDiagonalPolynomialBoundary_diagonal_rightAction (p : ZMod 2) (i : I)
    (v : List I) (c : Old D Sc cutoff v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v
      (outputCoefficientRightAction D Sc cutoff i
        (p + D.parity i * wordSumParity D v) v c f) =
    outputCoefficientRightAction D Sc cutoff i 0 v c
      (offDiagonalPolynomialBoundary D Sc cutoff p i v v f) := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  have h0 := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    (outputLongSection D Sc cutoff p i v f)
  rw [offDiagonalLongExtraction_diagonal, outputLongExtraction_section] at h0
  have h := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    (act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
      (outputLongSection D Sc cutoff p i v f))
  rw [offDiagonalLongExtraction_diagonal, outputLongExtraction_rightAction,
    outputLongExtraction_section] at h
  rw [pMap_postcomp, appendC0_postcomp, h0] at h
  exact h.symm

theorem offDiagonalPolynomialBoundary_independentS_postcomp (p : ZMod 2) (i : I)
    (v : List I) (n : ℕ) (f : ℕ →₀ Old D Sc cutoff v v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v
      (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff i v n)) f) =
    Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff i v n))
      (offDiagonalPolynomialBoundary D Sc cutoff p i v v f) := by
  have he (q : ZMod 2) (h : ℕ →₀ Old D Sc cutoff v v) :
      outputCoefficientRightAction D Sc cutoff i q v
        (independentOutputS D Sc cutoff i v n) h =
      Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff i v n)) h := by
    ext m
    rw [outputCoefficientRightAction_apply, independentOutputS_oldTwist]
    rfl
  have h := offDiagonalPolynomialBoundary_diagonal_rightAction D Sc cutoff p i v
    (independentOutputS D Sc cutoff i v n) f
  simpa only [he] using h

/-- Evaluation of independent S in the ordinary even coefficient shift. -/
def evenSAtShift (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
    (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff i v n))).comp
        ((evenLongShift D Sc cutoff v v) ^ n)

/-- The S boundary defect is confined below the independently proved S bound. -/
theorem offDiagonalPolynomialBoundary_even_S_high (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v)
    (m : ℕ) (hm : outputSDegree D i v ≤ m) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v (evenSAtShift D Sc cutoff i v f) m =
    independentSRightProduct D Sc cutoff i v
      (offDiagonalPolynomialBoundary D Sc cutoff p i v v f) m := by
  rw [independentSRightProduct_even_high D Sc cutoff i hi v _ m hm]
  simp only [evenSAtShift, LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply,
    map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [offDiagonalPolynomialBoundary_independentS_postcomp]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, LinearMap.flip_apply]
  have hs := independentOutputS_support D Sc cutoff i v hn
  rw [Finset.mem_range] at hs
  have he : m = n + (m - n) := by omega
  rw [he, offDiagonalPolynomialBoundary_even_iterate_high D Sc cutoff p i hi]
  simp only [Nat.add_sub_cancel_left]

theorem evenLongShift_iterate_single (v t : List I) (n m : ℕ)
    (b : Old D Sc cutoff v t) :
    (evenLongShift D Sc cutoff v t)^[n] (Finsupp.single m b) =
      Finsupp.single (n + m) b := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, evenLongShift_single]
    congr 1
    omega

private theorem evenPhi_oldComp_id (v : List I) (b : Old D Sc cutoff v v) :
    oldComp D Sc cutoff v v v ((ideal D Sc cutoff v v).mkQ (𝟙 _)) b = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  rw [oldComp_mk, Category.id_comp]

theorem evenSAtShift_single_id (i : I) (v : List I) (d : ℕ) :
    evenSAtShift D Sc cutoff i v
      (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))) =
    (evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v) := by
  have hs :
      (evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v) =
      ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
        Finsupp.single (d + n) (independentOutputS D Sc cutoff i v n) := by
    conv_lhs => rw [← Finsupp.sum_single (independentOutputS D Sc cutoff i v)]
    rw [← Module.End.coe_pow, Finsupp.sum, map_sum]
    simp only [Module.End.pow_apply, evenLongShift_iterate_single]
  rw [hs]
  simp only [evenSAtShift, LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply,
    evenLongShift_iterate_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    LinearMap.flip_apply, evenPhi_oldComp_id]
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.add_comm n d]

/-- The actual even diagonal row, evaluated on the full old identity class. -/
def evenBoundaryPhi (p : ZMod 2) (i : I) (v : List I) (d : ℕ) :
    ℕ →₀ Old D Sc cutoff v v :=
  offDiagonalPolynomialBoundary D Sc cutoff p i v v
    (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))

/-- High coefficients of S times the actual row are the ordered numerator coefficients. -/
theorem evenBoundaryPhi_S_high (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ) (hm : outputSDegree D i v ≤ m) :
    independentSRightProduct D Sc cutoff i v (evenBoundaryPhi D Sc cutoff p i v d) m =
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v)) m := by
  unfold evenBoundaryPhi
  rw [← offDiagonalPolynomialBoundary_even_S_high D Sc cutoff p i hi v _ m hm,
    evenSAtShift_single_id, offDiagonalPolynomialBoundary_even_independentS D Sc cutoff p i hi]

/-- The actual row vanishes above its prescribed bound, without a nonzero hypothesis. -/
theorem evenBoundaryPhi_above (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ)
    (hm : d + endpointQPDegree D cutoff i v < m + outputSDegree D i v) :
    evenBoundaryPhi D Sc cutoff p i v d m = 0 := by
  apply independentSRightProduct_even_detect_bound D Sc cutoff i hi v _
    (d + endpointQPDegree D cutoff i v) _ m hm
  intro n hn hN
  rw [evenBoundaryPhi_S_high D Sc cutoff p i hi v d n hn]
  exact appendC0_orderedReverseNumerator_above D Sc cutoff i v d n hN

/-- Its coefficient at the nonnegative-height bound is the prescribed scalar unit. -/
theorem evenBoundaryPhi_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) (hd : outputSDegree D i v ≤ d + endpointQPDegree D cutoff i v) :
    evenBoundaryPhi D Sc cutoff p i v d
      (d + endpointQPDegree D cutoff i v - outputSDegree D i v) =
    (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have ht := independentSRightProduct_even_top D Sc cutoff i hi v
    (evenBoundaryPhi D Sc cutoff p i v d)
    (d + endpointQPDegree D cutoff i v - outputSDegree D i v)
    (fun m hm => evenBoundaryPhi_above D Sc cutoff p i hi v d m (by omega))
  have he : d + endpointQPDegree D cutoff i v - outputSDegree D i v +
      outputSDegree D i v = d + endpointQPDegree D cutoff i v := by omega
  rw [he, evenBoundaryPhi_S_high D Sc cutoff p i hi v d _ hd,
    appendC0_orderedReverseNumerator_top] at ht
  exact ht.symm

end OddMath.QuiverHecke.ELVOld

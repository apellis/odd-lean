/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorCoefficients

/-!
# Polynomial boundary on the long section at an even moving colour

The polynomial row is the composite of the existing long section, P, and C₀.
The factorization is on the original prepend-old quotient, with arbitrary old
colours and full ELV coefficients. The reverse-numerator comparison below uses
this factorization and the diagrammatic even-dot identity; it does not posit a
monic polynomial row or a division equivalence.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The polynomial row on the specified long section, without a restriction on
old colours or on the parity normalization of old coefficients. -/
def evenPolynomialBoundary (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (appendC0 D Sc cutoff i v v).comp
    ((pMap D Sc cutoff i v (v ++ [i])).comp (outputLongSection D Sc cutoff p i v))

/-- The section composite factors C₀P through the original long extraction.
This factorization itself holds for either moving parity. -/
theorem evenPolynomialBoundary_factor (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    appendC0 D Sc cutoff i v v (pMap D Sc cutoff i v (v ++ [i]) z) =
      evenPolynomialBoundary D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z) := by
  have hs : z - outputLongSection D Sc cutoff p i v
      (outputLongExtraction D Sc cutoff p i v z) ∈
        chronologicalShortSpan D Sc cutoff i v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v]
    change outputLongExtraction D Sc cutoff p i v _ = 0
    rw [map_sub, outputLongExtraction_section, sub_self]
  have h := pMap_chronologicalShortSpan_le D Sc cutoff i v v
    (Submodule.mem_map.mpr ⟨_, hs, rfl⟩)
  rw [chronologicalCrossingSpan_eq_appendCrossingSpan, ← appendC0_ker,
    LinearMap.mem_ker, map_sub, map_sub, sub_eq_zero] at h
  exact h

/-- Evaluation at any full old coefficient is literally the C₀P-image of its
normalized PBW lift, not an independently supplied polynomial. -/
theorem evenPolynomialBoundary_single (p : ZMod 2) (i : I) (v : List I)
    (d : ℕ) (b : Old D Sc cutoff v v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) =
      appendC0 D Sc cutoff i v v
        (pMap D Sc cutoff i v (v ++ [i]) (outputLongLift D Sc cutoff p i v d b)) := by
  simp only [evenPolynomialBoundary, LinearMap.comp_apply, outputLongSection_single]

/-- The diagrammatic reverse numerator computes the row on the extracted
moving-dot iterate. No condition is imposed on old-word parities. -/
theorem evenPolynomialBoundary_reverseNumerator (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (d : ℕ) :
    evenPolynomialBoundary D Sc cutoff p i v
      (outputLongExtraction D Sc cutoff p i v
        ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d]
          (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)))) =
      inputCoefficientShift D Sc cutoff i v d
        (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff i v)) := by
  rw [← evenPolynomialBoundary_factor]
  have h := pMap_evenDot_move_iterate D Sc cutoff i hi v (v ++ [i]) d (𝟙 _)
  simp only [Category.comp_id] at h
  rw [h, appendC0_orderedReverseNumerator]

/-- At exponent zero the independent square product is linked to the actual
row by the existing intertwiner extraction and the reverse-numerator identity. -/
theorem evenPolynomialBoundary_independentS (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) :
    evenPolynomialBoundary D Sc cutoff p i v (independentOutputS D Sc cutoff i v) =
      orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
        (endpointOutputCoefficients D Sc cutoff i v) := by
  have h := evenPolynomialBoundary_reverseNumerator D Sc cutoff p i hi v 0
  have hs := outputLongExtraction_move_independentS D Sc cutoff p i v
  simp only [hi, SKM.zsign, zero_ne_one, ↓reduceIte, one_pow, one_smul] at hs
  change outputLongExtraction D Sc cutoff p i v
    (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)) = _ at hs
  simp only [Function.iterate_zero, id_eq, hs] at h
  have hz (f : ℕ →₀ Old D Sc cutoff v v) : inputCoefficientShift D Sc cutoff i v 0 f = f := by
    ext n
    have h := inputCoefficientShift_apply_add D Sc cutoff i v 0 f n
    simp only [zero_add, zero_nsmul] at h
    rw [h]
    obtain ⟨c, hc⟩ := (ideal D Sc cutoff v v).mkQ_surjective (f n)
    rw [← hc]
    change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
    rw [twist_zero]
  rw [hz] at h
  exact h

end OddMath.QuiverHecke.ELVOld

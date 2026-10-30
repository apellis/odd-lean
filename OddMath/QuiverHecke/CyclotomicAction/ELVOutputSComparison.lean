/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVLeadingSourceTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputMoveComparison
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveSquareProduct

/-!
# The independent ordered-product boundary coefficients

The polynomial below is defined by the independent ordered-product choices,
not by an extractor. The genuine source expansion and termwise transport identify
its coefficients with output extraction, with the library's fixed global sign.
This is the fixed-word polynomial comparison for `DeformedBoundaryDivision.md`
§§1, 4 in the library crossing convention of `MackeyCrossingConventions.md`.
It is not the corrected-rho iterate comparison, boundary division or prescribed inverse.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The signed independent ordered-product coefficient row. -/
def orderedOutputCoefficients (i : I) (v : List I) : ℕ →₀ Old D Sc cutoff v v :=
  ∑ c : MoveChoices v, leadingMoveCoeff D (k := k) i v c •
    Finsupp.single (sourceMovingDegree (leadingSourceDots D i 0 0 v c))
      ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c))

/-- The unsigned ordered S polynomial, specified by explicit independent
monomials and coefficients. The global sign removes the signed local factors. -/
def independentOutputS (i : I) (v : List I) : ℕ →₀ Old D Sc cutoff v v :=
  SKM.zsign k (D.parity i) ^ v.count i • orderedOutputCoefficients D Sc cutoff i v

/-- Fully explicit independent coefficient formula. The finite choices and old
dot monomials come from the ordered square product, not from extraction. -/
theorem independentOutputS_apply (i : I) (v : List I) (n : ℕ) :
    independentOutputS D Sc cutoff i v n =
      SKM.zsign k (D.parity i) ^ v.count i •
        ∑ c : MoveChoices v,
          if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
            leadingMoveCoeff D (k := k) i v c •
              (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
          else 0 := by
  simp only [independentOutputS, orderedOutputCoefficients, Finsupp.smul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

private theorem global_sign_square (i : I) (v : List I) :
    (SKM.zsign k (D.parity i) ^ v.count i) *
      (SKM.zsign k (D.parity i) ^ v.count i) = 1 := by
  rw [← mul_pow]
  by_cases hi : D.parity i = 1 <;> simp [SKM.zsign, hi]

/-- Extraction of the independent source expansion, evaluated term by term. -/
theorem outputLongExtraction_source_expansion (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          ((∑ c : MoveChoices v, leadingMoveCoeff D (k := k) i v c •
            endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c)) ≫
            OutputOldComposite.bareU D Sc i v))) =
      orderedOutputCoefficients D Sc cutoff i v := by
  simp only [Preadditive.sum_comp, Linear.smul_comp, map_sum, map_smul,
    leading_source_output_extraction, orderedOutputCoefficients]

/-- The independent unsigned ordered square product extracts to the explicit S
coefficient row; S is not defined by this equation. -/
theorem outputLongExtraction_squareProduct (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (leadingMoveSquareProduct D Sc i [] v ≫ OutputOldComposite.bareU D Sc i v))) =
      independentOutputS D Sc cutoff i v := by
  have h := outputLongExtraction_source_expansion D Sc cutoff p i v
  rw [leadingSource_expansion_eq_sign_smul] at h
  change outputLongExtraction D Sc cutoff p i v
    (projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        ((SKM.zsign k (D.parity i) ^ v.count i • leadingMoveSquareProduct D Sc i [] v) ≫
          OutputOldComposite.bareU D Sc i v))) = _ at h
  rw [Linear.smul_comp, map_smul, map_smul, map_smul] at h
  rw [independentOutputS, ← h, smul_smul, global_sign_square, one_smul]

/-- The actual moving intertwiner extracts to the independent S polynomial with
the fixed global library sign, for arbitrary words and both moving parities. -/
theorem outputLongExtraction_move_independentS (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v))) =
      SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v := by
  have h := outputLongExtraction_move_endpointPolynomial D Sc cutoff p i v 1
  change outputLongExtraction D Sc cutoff p i v
    (projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v))) =
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (leadingMoveEndpointPolynomial D Sc i [] v ≫ OutputOldComposite.bareU D Sc i v))) at h
  rw [h, leadingMoveEndpointPolynomial_eq_sign_smul_squareProduct,
    Linear.smul_comp, map_smul, map_smul, map_smul, outputLongExtraction_squareProduct]

/-- Literal finite coefficient formula, including the prescribed old composition
order and arbitrary full exterior old quotient coefficient on the source side. -/
theorem outputLongCoordinate_move_independentS_balanced (p : ZMod 2) (i : I) (v : List I)
    (b : Old D Sc cutoff v v) (n : ℕ) :
    outputLongCoordinate D Sc cutoff p i v n
      (balancedForward D Sc cutoff p i v (v ++ [i])
        (balancedTmul D Sc cutoff p i
          (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v)) b)) =
      oldComp D Sc cutoff v v v b
        (SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v n) := by
  rw [outputLongCoordinate_balanced]
  have h := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f n)
    (outputLongExtraction_move_independentS D Sc cutoff p i v)
  rw [outputLongExtraction_apply, Finsupp.smul_apply] at h
  rw [h]

end OddMath.QuiverHecke.ELVOld

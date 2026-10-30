/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendC0Candidate
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSIterates

/-!
# Polynomial projection of the prescribed boundary

The factorization in `DeformedMackeyBoundary.md` (5) holds on the original
prepend-old quotient column, not on a replacement crossing-image domain.
The independent S comparison projects the checked reverse-boundary identity
through the constructed C₀. It retains both signs and the ordered numerator.
No monic division or prescribed balanced crossing-column inverse is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The two existing crossing spans have the same arbitrary old-arrow generators. -/
theorem chronologicalCrossingSpan_eq_appendCrossingSpan (i : I) (v t : List I) :
    chronologicalCrossingSpan D Sc cutoff i v t = appendCrossingSpan D Sc cutoff i v t := by
  unfold chronologicalCrossingSpan appendCrossingSpan
  congr 1
  ext z
  constructor
  · rintro ⟨s, r, g, h⟩
    exact ⟨s, r, g, h.symm⟩
  · rintro ⟨s, r, g, h⟩
    exact ⟨s, r, g, h.symm⟩

/-- The boundary on long polynomial coordinates uses the specified PBW section. -/
def outputPolynomialBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) : (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (appendC0 D Sc cutoff j.1 v v).comp (outputLiftBoundary D Sc cutoff p j v)

/-- C₀P factors through the actual long extraction on the original source column. -/
theorem appendC0_pMap (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    appendC0 D Sc cutoff j.1 v v (pMap D Sc cutoff j.1 v (v ++ [j.1]) z) =
      outputPolynomialBoundary D Sc cutoff p j v
        (outputLongExtraction D Sc cutoff p j.1 v z) := by
  have h := pMap_sub_outputLiftBoundary_mem D Sc cutoff p j v z
  rw [chronologicalCrossingSpan_eq_appendCrossingSpan, ← appendC0_ker,
    LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h

/-- The independently defined S, evaluated at the corrected coefficient rho,
compares with the ordered reverse numerator after the actual polynomial projection.
The exponent is iterate parity; the moving colour is explicitly odd. -/
theorem outputPolynomialBoundary_independentS (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    SKM.zsign k (D.parity j.1) ^ v.count j.1 •
      outputPolynomialBoundary D Sc cutoff p j v
        (∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          Finsupp.mapRange.linearMap
            ((oldComp D Sc cutoff v v v).flip (independentOutputS D Sc cutoff j.1 v n))
            ((outputCoefficientRho D Sc cutoff p j v)^[n]
              (outputLongExtraction D Sc cutoff p j.1 v
                (outputCorrectedLift D Sc cutoff p j v d
                  ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendC0 D Sc cutoff j.1 v v
        (appendProjection D Sc cutoff j.1 v (v ++ [j.1])
          (appendMovingPower D Sc cutoff j.1 v d ≫
            affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
            endpointELV D Sc cutoff j.1 v)) := by
  have h := appendC0_pMap D Sc cutoff p j v
    ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
      (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v)))
  have hp := pMap_boundaryRho_move_iterate D Sc cutoff j v (v ++ [j.1]) d (𝟙 _)
  simp only [Category.comp_id] at hp
  rw [hp, map_smul] at h
  change _ = outputPolynomialBoundary D Sc cutoff p j v
    (outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff _ _ (moveHom D Sc j.1 [] v))))) at h
  rw [outputLongExtraction_boundaryRho_move_polynomial, map_smul] at h
  exact h.symm

end OddMath.QuiverHecke.ELVOld

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputKernel
import OddMath.QuiverHecke.CyclotomicAction.LeadingMovePolynomial

/-!
# Moving-chain comparison in long output coordinates

The prescribed moving chain and its collected endpoint polynomial have equal
long output extraction, with arbitrary exterior coefficients. Their difference
is therefore chronological short. This is the polynomial comparison needed
for S evaluation in `DeformedMackeyBoundary.md`; it does not identify the
normalized polynomial coefficients with the corrected rho iterates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem cast_map_apply_eq (i : I) (v t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
    (z z' : Target D Sc cutoff i v (v ++ [i])) (h : f z = f z') :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
      Old D Sc cutoff v t) e) f) z =
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
      Old D Sc cutoff v t) e) f) z' := by
  cases e
  exact h

/-- Full exterior coefficients preserve the collected moving-chain comparison. -/
theorem outputLongExtraction_move_endpointPolynomial (p : ZMod 2) (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i]) (a ⊗ₜ[k] moveHom D Sc i [] v)) =
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (a ⊗ₜ[k] (leadingMoveEndpointPolynomial D Sc i [] v ≫
          cl D Sc _ _ (cw (leadingMoveWord [] v)) (leadingMoveWord_sChain i [] v)))) := by
  ext m
  simp only [outputLongExtraction_apply]
  unfold outputLongCoordinate
  apply cast_map_apply_eq D Sc cutoff i v _ v (longOutputIndex_oldTarget i v m)
  simp only [LinearMap.smul_apply, prependOldCoordinate_projection]
  apply congrArg (fun b : Old D Sc cutoff v (longOutputIndex i v m).oldTarget =>
    (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • b)
  change (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
      (prependExtractOld D Sc cutoff p (longOutputIndex i v m) _) =
    (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
      (prependExtractOld D Sc cutoff p (longOutputIndex i v m) _)
  apply congrArg (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
  apply prependExtractOld_congr_long D Sc cutoff p (longOutputIndex i v m) rfl
  intro y hy
  rw [prependAffineEquiv_tmul, prependAffineEquiv_tmul,
    moveHom_long_prepend_repr_endpointPolynomial D Sc i v y hy]

/-- The moving chain differs from its collected polynomial by chronological short terms. -/
theorem move_sub_endpointPolynomial_mem_chronologicalShortSpan
    (p : ZMod 2) (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    projection D Sc cutoff i v (v ++ [i])
      (a ⊗ₜ[k] moveHom D Sc i [] v) -
    projection D Sc cutoff i v (v ++ [i])
      (a ⊗ₜ[k] (leadingMoveEndpointPolynomial D Sc i [] v ≫
        cl D Sc _ _ (cw (leadingMoveWord [] v)) (leadingMoveWord_sChain i [] v))) ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v]
  change outputLongExtraction D Sc cutoff p i v _ = 0
  rw [map_sub, outputLongExtraction_move_endpointPolynomial, sub_self]

end OddMath.QuiverHecke.ELVOld

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial

/-! # Polynomial quotient of the prescribed source column

The source cokernel in `DeformedMackeyBoundary.md` is identified with the
existing long polynomial coordinates. The prescribed P induces the existing
odd polynomial boundary on this quotient. No crossing-column injectivity,
bimodule naturality or inverse categorical matrix is assumed or asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The cokernel of the independently prescribed alpha column has the existing
polynomial old coordinates, using the proved kernel equality. -/
def sourceQuotientEquiv (p : ZMod 2) (i : I) (v : List I) :
    (Target D Sc cutoff i v (v ++ [i]) ⧸ LinearMap.range (alpha D Sc cutoff i v v)) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  (Submodule.quotEquivOfEq _ _ (ker_outputLongExtraction_eq_range_alpha D Sc cutoff p i v).symm).trans
    ((outputLongExtraction D Sc cutoff p i v).quotKerEquivOfSurjective
      (fun f => ⟨sourceLongSection D Sc cutoff p i v f,
        outputLongExtraction_sourceLongSection D Sc cutoff p i v f⟩))

@[simp] theorem sourceQuotientEquiv_mk (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    sourceQuotientEquiv D Sc cutoff p i v ((LinearMap.range (alpha D Sc cutoff i v v)).mkQ z) =
      outputLongExtraction D Sc cutoff p i v z := rfl

@[simp] theorem sourceQuotientEquiv_symm_apply (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    (sourceQuotientEquiv D Sc cutoff p i v).symm f =
      (LinearMap.range (alpha D Sc cutoff i v v)).mkQ (sourceLongSection D Sc cutoff p i v f) := by
  apply (sourceQuotientEquiv D Sc cutoff p i v).injective
  rw [LinearEquiv.apply_symm_apply, sourceQuotientEquiv_mk,
    outputLongExtraction_sourceLongSection]

/-- The prescribed polynomial row on the source decomposition is independent
of the short coordinate, for every long normalization parity. -/
theorem appendC0_pMap_sourceCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (a : PprimeDomain D Sc cutoff j.1 v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    appendC0 D Sc cutoff j.1 v v (pMap D Sc cutoff j.1 v (v ++ [j.1])
      ((sourceCoordinateEquiv D Sc cutoff p j.1 v).symm (a, f))) =
        outputPolynomialBoundary D Sc cutoff p j v f := by
  rw [appendC0_pMap D Sc cutoff p j v, sourceCoordinateEquiv_symm_apply, map_add,
    outputLongExtraction_alpha, outputLongExtraction_sourceLongSection, zero_add]

/-- C₀P vanishes on the prescribed alpha source, not just an auxiliary span. -/
theorem appendC0_pMap_alpha (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (a : PprimeDomain D Sc cutoff j.1 v v) :
    appendC0 D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1]) (alpha D Sc cutoff j.1 v v a)) = 0 := by
  rw [appendC0_pMap D Sc cutoff p j v, outputLongExtraction_alpha, map_zero]

/-- Descent of the prescribed composite C₀P through the alpha cokernel. -/
def sourceQuotientBoundary (j : {j : I // D.parity j = 1}) (v : List I) :
    (Target D Sc cutoff j.1 v (v ++ [j.1]) ⧸ LinearMap.range (alpha D Sc cutoff j.1 v v)) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  (LinearMap.range (alpha D Sc cutoff j.1 v v)).liftQ
    (appendC0 D Sc cutoff j.1 v v ∘ₗ pMap D Sc cutoff j.1 v (v ++ [j.1])) (by
      rintro z ⟨a, rfl⟩
      exact appendC0_pMap_alpha D Sc cutoff 0 j v a)

/-- The induced row is the existing polynomial boundary after the concrete
alpha-cokernel equivalence. -/
theorem sourceQuotientBoundary_eq (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    sourceQuotientBoundary D Sc cutoff j v =
      outputPolynomialBoundary D Sc cutoff p j v ∘ₗ
        (sourceQuotientEquiv D Sc cutoff p j.1 v).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (LinearMap.range (alpha D Sc cutoff j.1 v v)).mkQ_surjective z
  exact appendC0_pMap D Sc cutoff p j v z

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

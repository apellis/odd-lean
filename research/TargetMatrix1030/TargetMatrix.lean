/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial

/-! # Prescribed balanced target coordinates and the P matrix

This implements the tensor-matrix step of `DeformedMatrixComparison.md`, using
independently balanced short modules on both sides. The off-diagonal column is
retained. The output-dot formula retains its polynomial-constant error; no
categorical inverse or equivariance of the coordinate projections is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open ShortCrossCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

@[simp] theorem appendC0_shortCross (i : I) (v t : List I)
    (b : ShortTarget D Sc cutoff i v t) :
    appendC0 D Sc cutoff i v t (shortCross D Sc cutoff i v t b) = 0 := by
  have h : shortCross D Sc cutoff i v t b ∈
      LinearMap.range (shortCross D Sc cutoff i v t) := ⟨b, rfl⟩
  rw [range_shortCross, ← appendC0_ker] at h
  exact h

/-- Reconstruction with the independent short module and the unchanged polynomial section. -/
theorem target_reconstruction (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z) +
      appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) = z := by
  have hz := appendC0_residual_mem D Sc cutoff i v t z
  rw [← range_shortCross] at hz
  obtain ⟨b, hb⟩ := hz
  have hd := congrArg (decode D Sc cutoff i v t) hb
  simp only [decode_shortCross, map_sub, decode_embedding, sub_zero] at hd
  rw [← hd, hb]
  exact sub_add_cancel _ _

/-- The target coordinates use the prescribed decoder, not an image-span coordinate. -/
def targetCoordinateEquiv (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) ≃ₗ[k]
      (ShortTarget D Sc cutoff i v t × (ℕ →₀ Old D Sc cutoff v t)) where
  toLinearMap := (decode D Sc cutoff i v t).prod (appendC0 D Sc cutoff i v t)
  invFun b := shortCross D Sc cutoff i v t b.1 + appendOutputEmbedding D Sc cutoff i v t b.2
  left_inv := target_reconstruction D Sc cutoff i v t
  right_inv b := by
    apply Prod.ext
    · change decode D Sc cutoff i v t (_ + _) = b.1
      simp only [map_add, decode_shortCross, decode_embedding, add_zero]
    · change appendC0 D Sc cutoff i v t (_ + _) = b.2
      simp only [map_add, appendC0_shortCross, appendC0_embedding, zero_add]

@[simp] theorem targetCoordinateEquiv_apply (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    targetCoordinateEquiv D Sc cutoff i v t z =
      (decode D Sc cutoff i v t z, appendC0 D Sc cutoff i v t z) := rfl

@[simp] theorem targetCoordinateEquiv_symm_apply (i : I) (v t : List I)
    (b : ShortTarget D Sc cutoff i v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    (targetCoordinateEquiv D Sc cutoff i v t).symm (b, f) =
      shortCross D Sc cutoff i v t b + appendOutputEmbedding D Sc cutoff i v t f := rfl

/-- The off-diagonal correction uses the prescribed corrected source section. -/
def pMapOffDiagonal (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] ShortTarget D Sc cutoff i v v :=
  decode D Sc cutoff i v v ∘ₗ pMap D Sc cutoff i v (v ++ [i]) ∘ₗ
    sourceLongSection D Sc cutoff p i v

/-- Both components of the original P map on every prescribed source coordinate. -/
theorem pMap_targetCoordinates (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    targetCoordinateEquiv D Sc cutoff i v v
      (pMap D Sc cutoff i v (v ++ [i])
        ((sourceCoordinateEquiv D Sc cutoff p i v).symm (a, f))) =
      (pprime D Sc cutoff i v v a + pMapOffDiagonal D Sc cutoff p i v f,
        evenPolynomialBoundary D Sc cutoff p i v f) := by
  apply Prod.ext
  · change decode D Sc cutoff i v v (pMap D Sc cutoff i v (v ++ [i]) _) = _
    simp only [pMap_sourceCoordinateEquiv_symm,
      map_add, decode_shortCross, pMapOffDiagonal, LinearMap.comp_apply]
  · change appendC0 D Sc cutoff i v v (pMap D Sc cutoff i v (v ++ [i]) _) = _
    rw [evenPolynomialBoundary_factor, sourceCoordinateEquiv_symm_apply, map_add,
      outputLongExtraction_alpha, outputLongExtraction_sourceLongSection, zero_add]

/-- Literal whole-map equality, with the original P and independently fixed coordinates. -/
theorem pMap_triangular_matrix (p : ZMod 2) (i : I) (v : List I) :
    (targetCoordinateEquiv D Sc cutoff i v v).toLinearMap ∘ₗ
      pMap D Sc cutoff i v (v ++ [i]) ∘ₗ
        (sourceCoordinateEquiv D Sc cutoff p i v).symm.toLinearMap =
    ((pprime D Sc cutoff i v v ∘ₗ LinearMap.fst k _ _ +
      pMapOffDiagonal D Sc cutoff p i v ∘ₗ LinearMap.snd k _ _).prod
      (evenPolynomialBoundary D Sc cutoff p i v ∘ₗ LinearMap.snd k _ _)) := by
  apply LinearMap.ext
  intro x
  exact pMap_targetCoordinates D Sc cutoff p i v x.1 x.2

/-- On odd colours the uniform section-defined row is the previously constructed row. -/
theorem evenPolynomialBoundary_eq_polynomialBoundary (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    evenPolynomialBoundary D Sc cutoff p j v = outputPolynomialBoundary D Sc cutoff p j v := by
  apply LinearMap.ext
  intro f
  change appendC0 D Sc cutoff j v v
    (pMap D Sc cutoff j v (v ++ [j.1]) (outputLongSection D Sc cutoff p j v f)) = _
  rw [appendC0_pMap, outputLongExtraction_section]

/-- Output-dot short coordinate: the polynomial section contributes no crossing term. -/
theorem decode_outputDot (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    decode D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t z) =
      decode D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t
        (shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z))) := by
  conv_lhs => rw [← target_reconstruction D Sc cutoff i v t z]
  rw [map_add, map_add, appendOutputDot_embedding, decode_embedding, add_zero]

/-- The polynomial-constant output-dot error depends only on the independent short coordinate. -/
theorem appendC0Defect_shortCoordinate (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0Defect D Sc cutoff i v t z =
      appendC0 D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t
        (shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z))) := by
  conv_lhs => rw [← target_reconstruction D Sc cutoff i v t z]
  rw [map_add, appendC0Defect_embedding, add_zero]
  simp only [appendC0Defect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendC0_shortCross, map_zero, sub_zero]

/-- Complete output-dot coordinates, retaining the nonzero polynomial-constant error. -/
theorem targetCoordinateEquiv_outputDot (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    targetCoordinateEquiv D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t z) =
      (decode D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t
        (shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z))),
       appendOutputShift D Sc cutoff v t (appendC0 D Sc cutoff i v t z) +
        Finsupp.single 0 (appendC0 D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t
          (shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z))) 0)) := by
  apply Prod.ext
  · exact decode_outputDot D Sc cutoff i v t z
  · have h := appendC0Defect_degreeZero D Sc cutoff i v t z
    rw [appendC0Defect_shortCoordinate D Sc cutoff i v t z] at h
    change appendC0 D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t z) = _
    rw [← h, ← appendC0Defect_shortCoordinate]
    simp only [appendC0Defect, LinearMap.sub_apply, LinearMap.comp_apply]
    abel

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

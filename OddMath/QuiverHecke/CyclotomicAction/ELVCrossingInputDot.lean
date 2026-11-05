import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates

/-! # The input moving dot on the prescribed crossing source

The existing append moving operator is transported through the concrete
crossing decoder. Corrected rho and the actual short-column square prove
preservation of the Pprime relations, so the operator descends to the
independently prescribed cyclotomic source. This is input-oriented and
is not yet identified with the categorical signed-dot normalization.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def crossingInputDotAffine (j : {j : I // D.parity j = 1}) (v : List I) :
    ShortTarget D Sc cutoff j.1 v v →ₗ[k] ShortTarget D Sc cutoff j.1 v v :=
  ShortCrossCoordinates.decode D Sc cutoff j.1 v v ∘ₗ
    appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1 ∘ₗ
      shortCross D Sc cutoff j.1 v v

/-- The concrete decoder retains the crossing residual and removes exactly
the existing output-polynomial coordinate. -/
theorem shortCross_decode_residual (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) =
      z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) := by
  have hz := appendC0_residual_mem D Sc cutoff i v t z
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, hy⟩ := hz
  have hd := congrArg (ShortCrossCoordinates.decode D Sc cutoff i v t) hy
  simp only [ShortCrossCoordinates.decode_shortCross, map_sub,
    ShortCrossCoordinates.decode_embedding, sub_zero] at hd
  rw [hd] at hy
  exact hy

/-- The exact first-order transport includes its polynomial cap correction. -/
theorem shortCross_crossingInputDotAffine (j : {j : I // D.parity j = 1})
    (v : List I) (z : ShortTarget D Sc cutoff j.1 v v) :
    shortCross D Sc cutoff j.1 v v (crossingInputDotAffine D Sc cutoff j v z) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v v z) -
      appendOutputEmbedding D Sc cutoff j.1 v v
        (appendC0InputDefect D Sc cutoff j.1 v v (shortCross D Sc cutoff j.1 v v z)) := by
  have hzero : appendC0 D Sc cutoff j.1 v v (shortCross D Sc cutoff j.1 v v z) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff j.1 v v
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨z, rfl⟩
  have hdef : appendC0InputDefect D Sc cutoff j.1 v v (shortCross D Sc cutoff j.1 v v z) =
      appendC0 D Sc cutoff j.1 v v
        (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
          (shortCross D Sc cutoff j.1 v v z)) := by
    simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
      hzero, map_zero, sub_zero]
  change shortCross D Sc cutoff j.1 v v
    (ShortCrossCoordinates.decode D Sc cutoff j.1 v v _) = _
  rw [shortCross_decode_residual, hdef]
  rfl

/-- The moving input dot sends every Pprime relation to another Pprime relation. -/
theorem crossingInputDotAffine_pprime (j : {j : I // D.parity j = 1}) (v : List I)
    (a : PprimeDomain D Sc cutoff j.1 v v) :
    crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
      LinearMap.range (pprime D Sc cutoff j.1 v v) := by
  have hz : boundaryRho D Sc cutoff j v (v ++ [j.1]) (alpha D Sc cutoff j.1 v v a) ∈
      LinearMap.range (alpha D Sc cutoff j.1 v v) := by
    rw [← ker_outputLongExtraction_eq_range_alpha D Sc cutoff 0 j.1 v,
      LinearMap.mem_ker, outputLongExtraction_boundaryRho,
      outputLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff j.1 v v a' =
    ShortCrossCoordinates.decode D Sc cutoff j.1 v v
      (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v v (pprime D Sc cutoff j.1 v v a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_boundaryRho, ← ha', hs', ShortCrossCoordinates.decode_shortCross]

theorem crossingInputDotAffine_ker_q (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v v) ≤
      (LinearMap.ker (q D Sc cutoff j.1 v v)).comap
        (crossingInputDotAffine D Sc cutoff j v) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
    LinearMap.ker (q D Sc cutoff j.1 v v)
  rw [← range_pprime_eq_ker_q]
  exact crossingInputDotAffine_pprime D Sc cutoff j v a

/-- Concrete transport of the moving input dot to the original cyclotomic source. -/
def crossingInputDot (j : {j : I // D.parity j = 1}) (v : List I) :
    Source D Sc cutoff j.1 v v →ₗ[k] Source D Sc cutoff j.1 v v :=
  let e := (q D Sc cutoff j.1 v v).quotKerEquivOfSurjective (q_surjective D Sc cutoff j.1 v v)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff j.1 v v)).mapQ
      (LinearMap.ker (q D Sc cutoff j.1 v v)) (crossingInputDotAffine D Sc cutoff j v)
      (crossingInputDotAffine_ker_q D Sc cutoff j v) ∘ₗ e.symm.toLinearMap

@[simp] theorem crossingInputDot_q (j : {j : I // D.parity j = 1}) (v : List I)
    (z : ShortTarget D Sc cutoff j.1 v v) :
    crossingInputDot D Sc cutoff j v (q D Sc cutoff j.1 v v z) =
      q D Sc cutoff j.1 v v (crossingInputDotAffine D Sc cutoff j v z) := by
  simp only [crossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]


/-- Signed source-dot formula on full-coefficient representatives. -/
theorem crossingInputDotAffine_representative (j : {j : I // D.parity j = 1})
    (v s : List I) (r : hom D Sc cutoff v (s ++ [j.1]))
    (g : hom D Sc cutoff (s ++ [j.1]) v) :
    crossingInputDotAffine D Sc cutoff j v
      (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ r)) =
      SKM.zsign k (D.parity j.1 * D.parity j.1) •
        shortTensor D Sc cutoff j.1 v s v
          (appendMovingPower D Sc cutoff j.1 s 1 ≫ g)
          ((ideal D Sc cutoff v (s ++ [j.1])).mkQ (twist k (D.parity j.1) r)) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v v
    (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v v
        (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff _ _).mkQ r)))) = _
  rw [ShortCrossCoordinates.column_mk, appendMovingPowerTarget_crossing_one]
  simp only [map_sub, map_smul, ShortCrossCoordinates.decode_embedding, smul_zero, sub_zero]
  rw [← ShortCrossCoordinates.column_mk, ShortCrossCoordinates.decode_shortCross]

theorem crossingInputDot_iterate_q (j : {j : I // D.parity j = 1}) (v : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff j.1 v v) :
    (crossingInputDot D Sc cutoff j v)^[r] (q D Sc cutoff j.1 v v z) =
      q D Sc cutoff j.1 v v ((crossingInputDotAffine D Sc cutoff j v)^[r] z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, crossingInputDot_q, Function.iterate_succ_apply']

theorem inputContraction_iterate_q (j : {j : I // D.parity j = 1}) (v : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff j.1 v v) :
    inputContraction D Sc cutoff j v
      ((crossingInputDot D Sc cutoff j v)^[r] (q D Sc cutoff j.1 v v z)) =
      inputContractionAffine D Sc cutoff j v ((crossingInputDotAffine D Sc cutoff j v)^[r] z) := by
  rw [crossingInputDot_iterate_q, inputContraction_q]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

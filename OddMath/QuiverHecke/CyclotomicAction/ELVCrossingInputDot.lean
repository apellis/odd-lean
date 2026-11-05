import OddMath.QuiverHecke.CyclotomicAction.ELVCapCoordinateTransport

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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

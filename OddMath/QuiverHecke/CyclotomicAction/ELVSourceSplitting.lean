/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicAlphaCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputCompatibleLifts

/-! # Prescribed source and polynomial long coordinates

The source step of `DeformedMackeyBoundary.md` identifies the range of the
prescribed epsilon-balanced column with the chronological short span. On the
diagonal output this is the kernel of every normalized long extraction.
`sourceCoordinateEquiv` uses the existing decoder and a corrected PBW section,
not an independently chosen complement or an injectivity hypothesis.
The result is ground-ring linear; bimodule and categorical naturality are separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem range_alpha_eq_chronologicalShortSpan (i : I) (v t : List I) :
    LinearMap.range (alpha D Sc cutoff i v t) = chronologicalShortSpan D Sc cutoff i v t := by
  apply le_antisymm
  · have hz : (chronologicalShortSpan D Sc cutoff i v t).mkQ ∘ₗ
        alpha D Sc cutoff i v t = 0 := by
      apply BalancedInduction.hom_ext
      intro s h b
      change (chronologicalShortSpan D Sc cutoff i v t).mkQ
        (alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b)) = 0
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
      rw [alpha_tensor, alphaPair_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.subset_span ⟨s.word, twist k (epsilon D cutoff i v) r, h, rfl⟩
    rintro z ⟨a, rfl⟩
    have h := LinearMap.congr_fun hz a
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · apply Submodule.span_le.mpr
    rintro z ⟨s, r, h, rfl⟩
    refine ⟨pprimeTensor D Sc cutoff i v s t h
      ((ideal D Sc cutoff v (s ++ [i])).mkQ (twist k (epsilon D cutoff i v) r)), ?_⟩
    rw [alpha_tensor, alphaPair_mk, twist_twist]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

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

theorem ker_outputLongExtraction_eq_range_alpha (p : ZMod 2) (i : I) (v : List I) :
    LinearMap.ker (outputLongExtraction D Sc cutoff p i v) =
      LinearMap.range (alpha D Sc cutoff i v v) := by
  rw [ker_outputLongExtraction_eq_chronologicalShortSpan, range_alpha_eq_chronologicalShortSpan]

@[simp] theorem outputLongExtraction_alpha (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) :
    outputLongExtraction D Sc cutoff p i v (alpha D Sc cutoff i v v a) = 0 := by
  have h : alpha D Sc cutoff i v v a ∈ LinearMap.range (alpha D Sc cutoff i v v) := ⟨a, rfl⟩
  rw [← ker_outputLongExtraction_eq_range_alpha D Sc cutoff p i v] at h
  exact h

/-- The existing long lift corrected by its prescribed short-source coordinate. -/
def sourceLongSection (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  outputLongSection D Sc cutoff p i v -
    alpha D Sc cutoff i v v ∘ₗ extract D Sc cutoff i v v ∘ₗ outputLongSection D Sc cutoff p i v

@[simp] theorem extract_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    extract D Sc cutoff i v v (sourceLongSection D Sc cutoff p i v f) = 0 := by
  simp only [sourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    extract_alpha, sub_self]

@[simp] theorem outputLongExtraction_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v (sourceLongSection D Sc cutoff p i v f) = f := by
  simp only [sourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    outputLongExtraction_alpha, outputLongExtraction_section, sub_zero]

theorem source_reconstruction (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    alpha D Sc cutoff i v v (extract D Sc cutoff i v v z) +
      sourceLongSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z) = z := by
  have hz : z - sourceLongSection D Sc cutoff p i v
      (outputLongExtraction D Sc cutoff p i v z) ∈
      LinearMap.ker (outputLongExtraction D Sc cutoff p i v) := by
    simp only [LinearMap.mem_ker, map_sub, outputLongExtraction_sourceLongSection, sub_self]
  rw [ker_outputLongExtraction_eq_range_alpha] at hz
  obtain ⟨a, ha⟩ := hz
  have he := congrArg (extract D Sc cutoff i v v) ha
  simp only [extract_alpha, map_sub, extract_sourceLongSection, sub_zero] at he
  rw [← he, ha]
  exact sub_add_cancel _ _

/-- Coordinates in the prescribed balanced source and the existing polynomial old module. -/
def sourceCoordinateEquiv (p : ZMod 2) (i : I) (v : List I) :
    Target D Sc cutoff i v (v ++ [i]) ≃ₗ[k]
      (PprimeDomain D Sc cutoff i v v × (ℕ →₀ Old D Sc cutoff v v)) where
  toLinearMap := (extract D Sc cutoff i v v).prod (outputLongExtraction D Sc cutoff p i v)
  invFun a := alpha D Sc cutoff i v v a.1 + sourceLongSection D Sc cutoff p i v a.2
  left_inv := source_reconstruction D Sc cutoff p i v
  right_inv a := by
    apply Prod.ext
    · change extract D Sc cutoff i v v (_ + _) = a.1
      simp only [map_add, extract_alpha, extract_sourceLongSection, add_zero]
    · change outputLongExtraction D Sc cutoff p i v (_ + _) = a.2
      simp only [map_add, outputLongExtraction_alpha,
        outputLongExtraction_sourceLongSection, zero_add]

@[simp] theorem sourceCoordinateEquiv_apply (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    sourceCoordinateEquiv D Sc cutoff p i v z =
      (extract D Sc cutoff i v v z, outputLongExtraction D Sc cutoff p i v z) := rfl

@[simp] theorem sourceCoordinateEquiv_symm_apply (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    (sourceCoordinateEquiv D Sc cutoff p i v).symm (a, f) =
      alpha D Sc cutoff i v v a + sourceLongSection D Sc cutoff p i v f := rfl

@[simp] theorem sourceCoordinateEquiv_alpha (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) :
    sourceCoordinateEquiv D Sc cutoff p i v (alpha D Sc cutoff i v v a) = (a, 0) := by
  simp only [sourceCoordinateEquiv_apply, extract_alpha, outputLongExtraction_alpha]

/-- The polynomial projection is literally the existing long extraction. -/
theorem snd_comp_sourceCoordinateEquiv (p : ZMod 2) (i : I) (v : List I) :
    (LinearMap.snd k _ _) ∘ₗ (sourceCoordinateEquiv D Sc cutoff p i v).toLinearMap =
      outputLongExtraction D Sc cutoff p i v := rfl

/-- The short part of the prescribed P map is its original crossing-column square. -/
theorem pMap_sourceCoordinateEquiv_symm (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    pMap D Sc cutoff i v (v ++ [i]) ((sourceCoordinateEquiv D Sc cutoff p i v).symm (a, f)) =
      shortCross D Sc cutoff i v v (pprime D Sc cutoff i v v a) +
        pMap D Sc cutoff i v (v ++ [i]) (sourceLongSection D Sc cutoff p i v f) := by
  rw [sourceCoordinateEquiv_symm_apply, map_add]
  exact congrArg (fun z => z + pMap D Sc cutoff i v (v ++ [i])
    (sourceLongSection D Sc cutoff p i v f))
      (LinearMap.congr_fun (shortColumn_square D Sc cutoff i v v) a)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

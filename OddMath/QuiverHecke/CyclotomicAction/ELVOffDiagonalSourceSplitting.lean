import OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongKernel

/-! # Actual source splitting on arbitrary old Hom coefficients

The long extraction has the prescribed alpha range as its kernel. Correcting
the actual long section by its alpha coordinate gives the source normal form.
Both old endpoints are arbitrary; every moving colour is retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem ker_offDiagonalLongExtraction_eq_range_alpha (p : ZMod 2) (i : I) (v t : List I) :
    LinearMap.ker (offDiagonalLongExtraction D Sc cutoff p i v t) =
      LinearMap.range (alpha D Sc cutoff i v t) := by
  rw [ker_offDiagonalLongExtraction_eq_chronologicalShortSpan, range_alpha_eq_chronologicalShortSpan]

@[simp] theorem offDiagonalLongExtraction_alpha (p : ZMod 2) (i : I) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) :
    offDiagonalLongExtraction D Sc cutoff p i v t (alpha D Sc cutoff i v t a) = 0 := by
  have h : alpha D Sc cutoff i v t a ∈ LinearMap.range (alpha D Sc cutoff i v t) := ⟨a, rfl⟩
  rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p i v t] at h
  exact h

/-- The existing long lift corrected by its prescribed short-source coordinate. -/
def offDiagonalSourceLongSection (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Target D Sc cutoff i v (t ++ [i]) :=
  offDiagonalLongSection D Sc cutoff p i v t -
    alpha D Sc cutoff i v t ∘ₗ extract D Sc cutoff i v t ∘ₗ offDiagonalLongSection D Sc cutoff p i v t

@[simp] theorem extract_offDiagonalSourceLongSection (p : ZMod 2) (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    extract D Sc cutoff i v t (offDiagonalSourceLongSection D Sc cutoff p i v t f) = 0 := by
  simp only [offDiagonalSourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    extract_alpha, sub_self]

@[simp] theorem offDiagonalLongExtraction_sourceLongSection (p : ZMod 2) (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalLongExtraction D Sc cutoff p i v t (offDiagonalSourceLongSection D Sc cutoff p i v t f) = f := by
  simp only [offDiagonalSourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    offDiagonalLongExtraction_alpha, offDiagonalLongExtraction_section, sub_zero]

theorem offDiagonalSource_reconstruction (p : ZMod 2) (i : I) (v t : List I)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    alpha D Sc cutoff i v t (extract D Sc cutoff i v t z) +
      offDiagonalSourceLongSection D Sc cutoff p i v t (offDiagonalLongExtraction D Sc cutoff p i v t z) = z := by
  have hz : z - offDiagonalSourceLongSection D Sc cutoff p i v t
      (offDiagonalLongExtraction D Sc cutoff p i v t z) ∈
      LinearMap.ker (offDiagonalLongExtraction D Sc cutoff p i v t) := by
    simp only [LinearMap.mem_ker, map_sub, offDiagonalLongExtraction_sourceLongSection, sub_self]
  rw [ker_offDiagonalLongExtraction_eq_range_alpha] at hz
  obtain ⟨a, ha⟩ := hz
  have he := congrArg (extract D Sc cutoff i v t) ha
  simp only [extract_alpha, map_sub, extract_offDiagonalSourceLongSection, sub_zero] at he
  rw [← he, ha]
  exact sub_add_cancel _ _

/-- Coordinates in the prescribed balanced source and the existing polynomial old module. -/
def offDiagonalSourceCoordinateEquiv (p : ZMod 2) (i : I) (v t : List I) :
    Target D Sc cutoff i v (t ++ [i]) ≃ₗ[k]
      (PprimeDomain D Sc cutoff i v t × (ℕ →₀ Old D Sc cutoff v t)) where
  toLinearMap := (extract D Sc cutoff i v t).prod (offDiagonalLongExtraction D Sc cutoff p i v t)
  invFun a := alpha D Sc cutoff i v t a.1 + offDiagonalSourceLongSection D Sc cutoff p i v t a.2
  left_inv := offDiagonalSource_reconstruction D Sc cutoff p i v t
  right_inv a := by
    apply Prod.ext
    · change extract D Sc cutoff i v t (_ + _) = a.1
      simp only [map_add, extract_alpha, extract_offDiagonalSourceLongSection, add_zero]
    · change offDiagonalLongExtraction D Sc cutoff p i v t (_ + _) = a.2
      simp only [map_add, offDiagonalLongExtraction_alpha,
        offDiagonalLongExtraction_sourceLongSection, zero_add]

@[simp] theorem offDiagonalSourceCoordinateEquiv_apply (p : ZMod 2) (i : I) (v t : List I)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    offDiagonalSourceCoordinateEquiv D Sc cutoff p i v t z =
      (extract D Sc cutoff i v t z, offDiagonalLongExtraction D Sc cutoff p i v t z) := rfl

@[simp] theorem offDiagonalSourceCoordinateEquiv_symm_apply (p : ZMod 2) (i : I) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    (offDiagonalSourceCoordinateEquiv D Sc cutoff p i v t).symm (a, f) =
      alpha D Sc cutoff i v t a + offDiagonalSourceLongSection D Sc cutoff p i v t f := rfl

@[simp] theorem offDiagonalSourceCoordinateEquiv_alpha (p : ZMod 2) (i : I) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) :
    offDiagonalSourceCoordinateEquiv D Sc cutoff p i v t (alpha D Sc cutoff i v t a) = (a, 0) := by
  simp only [offDiagonalSourceCoordinateEquiv_apply, extract_alpha, offDiagonalLongExtraction_alpha]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

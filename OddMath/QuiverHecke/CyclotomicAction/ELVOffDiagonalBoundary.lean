import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial

/-! # The polynomial boundary over arbitrary old Homs

DeformedMackeyBoundary (5) factors the actual C₀P through the finite long
row. The source and target old words are independent, and all moving
colours are retained. This identifies the boundary map on real quotient
coordinates; its leading coefficient and division remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual polynomial boundary, evaluated on the prescribed long section. -/
def offDiagonalPolynomialBoundary (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (appendC0 D Sc cutoff i v t).comp
    ((pMap D Sc cutoff i v (t ++ [i])).comp
      (offDiagonalLongSection D Sc cutoff p i v t))

/-- C₀P factors through the actual arbitrary-old-Hom long row at every colour. -/
theorem appendC0_pMap_offDiagonal (p : ZMod 2) (i : I) (v t : List I)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    appendC0 D Sc cutoff i v t (pMap D Sc cutoff i v (t ++ [i]) z) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t
        (offDiagonalLongExtraction D Sc cutoff p i v t z) := by
  let d := z - offDiagonalLongSection D Sc cutoff p i v t
    (offDiagonalLongExtraction D Sc cutoff p i v t z)
  have hd : d ∈ chronologicalShortSpan D Sc cutoff i v t := by
    rw [← ker_offDiagonalLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v t,
      LinearMap.mem_ker]
    dsimp only [d]
    rw [map_sub, offDiagonalLongExtraction_section, sub_self]
  have hp := pMap_chronologicalShortSpan_le D Sc cutoff i v t
    (Submodule.mem_map_of_mem hd)
  rw [chronologicalCrossingSpan_eq_appendCrossingSpan, ← appendC0_ker,
    LinearMap.mem_ker] at hp
  dsimp only [d] at hp
  rw [map_sub, map_sub, sub_eq_zero] at hp
  exact hp

end OddMath.QuiverHecke.ELVOld

import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRowSplitting

/-! # Height consequences for the prescribed cyclotomic crossing

The polynomial boundary and actual short-column square give injectivity in
nonnegative KKO height and surjectivity in nonpositive KKO height. These are
diagram chases on the prescribed balanced source, not assumed snake data.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalToCyclotomic_injective_of_nonnegative_height (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (toCyclotomic D Sc cutoff j.1 v t) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
  have hy : shortCross D Sc cutoff j.1 v t y ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [LinearMap.mem_ker]
    have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
    exact he.trans hz
  rw [ker_canonicalAppendTarget] at hy
  obtain ⟨x, hx⟩ := hy
  have hc : appendC0 D Sc cutoff j.1 v t (shortCross D Sc cutoff j.1 v t y) = 0 := by
    have hm : shortCross D Sc cutoff j.1 v t y ∈
        appendCrossingSpan D Sc cutoff j.1 v t := by
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    rw [← appendC0_ker, LinearMap.mem_ker] at hm
    exact hm
  have hb : offDiagonalLongExtraction D Sc cutoff p j.1 v t x = 0 := by
    apply offDiagonalPolynomialBoundary_injective D Sc cutoff p j v t h
    rw [map_zero, ← appendC0_pMap_offDiagonal, hx]
    exact hc
  have hm : x ∈ LinearMap.range (alpha D Sc cutoff j.1 v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p j.1 v t,
      LinearMap.mem_ker]
    exact hb
  obtain ⟨a, ha⟩ := hm
  have he : pprime D Sc cutoff j.1 v t a = y := by
    apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j.1 v t
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.symm.trans (by rw [ha]; exact hx)
  have hq : pprime D Sc cutoff j.1 v t a ∈ LinearMap.ker (q D Sc cutoff j.1 v t) := by
    rw [← range_pprime_eq_ker_q]
    exact ⟨a, rfl⟩
  rw [LinearMap.mem_ker, he] at hq
  exact hq

theorem offDiagonalToCyclotomic_surjective_of_nonpositive_height (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    Function.Surjective (toCyclotomic D Sc cutoff j.1 v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j.1 v (t ++ [j.1]) n
  let f := offDiagonalBoundaryRowSection D Sc cutoff p j v t (appendC0 D Sc cutoff j.1 v t z)
  let x := offDiagonalSourceLongSection D Sc cutoff p j.1 v t f
  have hc : z - pMap D Sc cutoff j.1 v (t ++ [j.1]) x ∈
      appendCrossingSpan D Sc cutoff j.1 v t := by
    dsimp only [x, f]
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, appendC0_pMap_offDiagonal,
      offDiagonalLongExtraction_sourceLongSection, offDiagonalBoundaryRowSection_rightInverse D Sc cutoff p j v t h]
    exact sub_self _
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨q D Sc cutoff j.1 v t y, ?_⟩
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub]
  have hx : pMap D Sc cutoff j.1 v (t ++ [j.1]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx, sub_zero]

/-- At height zero the prescribed crossing itself is an equivalence. -/
def offDiagonalToCyclotomicEquiv_zero_height (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v) :
    Source D Sc cutoff j.1 v t ≃ₗ[k] Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff j.1 v t)
    ⟨offDiagonalToCyclotomic_injective_of_nonnegative_height D Sc cutoff p j v t h.ge,
      offDiagonalToCyclotomic_surjective_of_nonpositive_height D Sc cutoff p j v t h.le⟩

@[simp] theorem offDiagonalToCyclotomicEquiv_zero_height_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v)
    (z : Source D Sc cutoff j.1 v t) :
    offDiagonalToCyclotomicEquiv_zero_height D Sc cutoff p j v t h z =
      toCyclotomic D Sc cutoff j.1 v t z := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

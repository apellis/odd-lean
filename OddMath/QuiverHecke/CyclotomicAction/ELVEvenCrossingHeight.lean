import OddMath.QuiverHecke.CyclotomicAction.ELVEvenRowDivision
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundarySnake

/-! # Even crossing height consequences

The parity-zero polynomial division in DeformedBoundaryDivision (5) gives
injectivity or surjectivity of the prescribed balanced crossing in the two
height ranges of DeformedRouquierMatrix, section 4. The same generic snake
comparison identifies its kernel with the even polynomial boundary kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenToCyclotomic_injective_of_nonnegative_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : outputSDegree D j v ≤ endpointQPDegree D cutoff j v) :
    Function.Injective (toCyclotomic D Sc cutoff j v t) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j v t z
  have hy : shortCross D Sc cutoff j v t y ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [LinearMap.mem_ker]
    have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
    exact he.trans hz
  rw [ker_canonicalAppendTarget] at hy
  obtain ⟨x, hx⟩ := hy
  have hc : appendC0 D Sc cutoff j v t (shortCross D Sc cutoff j v t y) = 0 := by
    have hm : shortCross D Sc cutoff j v t y ∈
        appendCrossingSpan D Sc cutoff j v t := by
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    rw [← appendC0_ker, LinearMap.mem_ker] at hm
    exact hm
  have hb : offDiagonalLongExtraction D Sc cutoff p j v t x = 0 := by
    apply offDiagonalPolynomialBoundary_even_injective D Sc cutoff p j hj v t h
    rw [map_zero, ← appendC0_pMap_offDiagonal, hx]
    exact hc
  have hm : x ∈ LinearMap.range (alpha D Sc cutoff j v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p j v t,
      LinearMap.mem_ker]
    exact hb
  obtain ⟨a, ha⟩ := hm
  have he : pprime D Sc cutoff j v t a = y := by
    apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j v t
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.symm.trans (by rw [ha]; exact hx)
  have hq : pprime D Sc cutoff j v t a ∈ LinearMap.ker (q D Sc cutoff j v t) := by
    rw [← range_pprime_eq_ker_q]
    exact ⟨a, rfl⟩
  rw [LinearMap.mem_ker, he] at hq
  exact hq

theorem evenToCyclotomic_surjective_of_nonpositive_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v ≤ outputSDegree D j v) :
    Function.Surjective (toCyclotomic D Sc cutoff j v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j v (t ++ [j]) n
  obtain ⟨f, hf⟩ := offDiagonalPolynomialBoundary_even_surjective D Sc cutoff p j hj v t h
    (appendC0 D Sc cutoff j v t z)
  let x := offDiagonalSourceLongSection D Sc cutoff p j v t f
  have hc : z - pMap D Sc cutoff j v (t ++ [j]) x ∈
      appendCrossingSpan D Sc cutoff j v t := by
    dsimp only [x]
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, appendC0_pMap_offDiagonal,
      offDiagonalLongExtraction_sourceLongSection, hf]
    exact sub_self _
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨q D Sc cutoff j v t y, ?_⟩
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub]
  have hx : pMap D Sc cutoff j v (t ++ [j]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx, sub_zero]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

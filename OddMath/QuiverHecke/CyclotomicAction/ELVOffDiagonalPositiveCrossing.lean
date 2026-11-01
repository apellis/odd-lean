import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCrossingHeight

/-! # The prescribed crossing with the positive polynomial window

The nonnegative KKO-height branch of the matrix in
`DeformedRouquierMatrix.md` is the actual cyclotomic crossing augmented by
the literal low polynomial columns. Its bijectivity follows from the proved
arbitrary-Hom boundary division and the prescribed short-column diagram.
The old source and target words are independent.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def offDiagonalPositiveCrossingAssembly (j : {j : I // D.parity j = 1}) (v t : List I) :
    (Source D Sc cutoff j.1 v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) →ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (toCyclotomic D Sc cutoff j.1 v t).comp (LinearMap.fst k _ _) +
    (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])).comp
      ((appendOutputEmbedding D Sc cutoff j.1 v t).comp
        ((offDiagonalBoundaryRowWindow D Sc cutoff j v t).subtype.comp (LinearMap.snd k _ _)))

@[simp] theorem offDiagonalPositiveCrossingAssembly_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (s : Source D Sc cutoff j.1 v t)
    (r : offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    offDiagonalPositiveCrossingAssembly D Sc cutoff j v t (s, r) =
      toCyclotomic D Sc cutoff j.1 v t s +
        canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])
          (appendOutputEmbedding D Sc cutoff j.1 v t r) := rfl

theorem offDiagonalPositiveCrossingAssembly_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t) := by
  suffices hzero : ∀ z, offDiagonalPositiveCrossingAssembly D Sc cutoff j v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : offDiagonalPositiveCrossingAssembly D Sc cutoff j v t (x - y) = offDiagonalPositiveCrossingAssembly D Sc cutoff j v t x - offDiagonalPositiveCrossingAssembly D Sc cutoff j v t y :=
      map_sub (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  rintro ⟨s, r⟩ hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v t s
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
  simp only [LinearMap.comp_apply] at hs
  have hm : shortCross D Sc cutoff j.1 v t y + appendOutputEmbedding D Sc cutoff j.1 v t r ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [LinearMap.mem_ker, map_add, hs]
    exact hz
  rw [ker_canonicalAppendTarget] at hm
  obtain ⟨x, hx⟩ := hm
  have hc : appendC0 D Sc cutoff j.1 v t (shortCross D Sc cutoff j.1 v t y) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff j.1 v t
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨y, rfl⟩
  have hb : offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t x) = r := by
    rw [← appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t, hx, map_add, hc, appendC0_embedding, zero_add]
  have hrcoord : (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).symm r = (0, r) := by
    apply (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).injective
    rw [LinearEquiv.apply_symm_apply, offDiagonalBoundaryPositiveEquiv_apply, map_zero, zero_add]
  have hr : r = 0 := by
    have he := congrArg (fun z => ((offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).symm z).2) hb
    rw [offDiagonalBoundaryPositiveEquiv_symm_boundary, hrcoord] at he
    exact he.symm
  apply Prod.ext
  · change q D Sc cutoff j.1 v t y = 0
    apply offDiagonalToCyclotomic_injective_of_nonnegative_height D Sc cutoff p j v t h
    have hz' : toCyclotomic D Sc cutoff j.1 v t (q D Sc cutoff j.1 v t y) = 0 := by
      simpa only [offDiagonalPositiveCrossingAssembly_apply, hr, ZeroMemClass.coe_zero, map_zero, add_zero] using hz
    exact hz'.trans ((toCyclotomic D Sc cutoff j.1 v t).map_zero.symm)
  · exact hr

theorem offDiagonalPositiveCrossingAssembly_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Surjective (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j.1 v (t ++ [j.1]) n
  obtain ⟨⟨f, r⟩, hfr⟩ := (offDiagonalBoundaryPositiveAssembly_bijective D Sc cutoff p j v t h).2
    (appendC0 D Sc cutoff j.1 v t z)
  change offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t f + r =
    appendC0 D Sc cutoff j.1 v t z at hfr
  let x := offDiagonalSourceLongSection D Sc cutoff p j.1 v t f
  have hc : z - pMap D Sc cutoff j.1 v (t ++ [j.1]) x -
      appendOutputEmbedding D Sc cutoff j.1 v t r ∈ appendCrossingSpan D Sc cutoff j.1 v t := by
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, map_sub, appendC0_pMap_offDiagonal,
      appendC0_embedding]
    dsimp only [x]
    rw [offDiagonalLongExtraction_sourceLongSection, ← hfr]
    abel
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(q D Sc cutoff j.1 v t y, r), ?_⟩
  rw [offDiagonalPositiveCrossingAssembly_apply]
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub, map_sub]
  have hx : pMap D Sc cutoff j.1 v (t ++ [j.1]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx]
  abel

/-- The literal crossing and low polynomial columns form the positive branch. -/
def offDiagonalPositiveCrossingEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    (Source D Sc cutoff j.1 v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  LinearEquiv.ofBijective (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t)
    ⟨offDiagonalPositiveCrossingAssembly_injective D Sc cutoff p j v t h,
      offDiagonalPositiveCrossingAssembly_surjective D Sc cutoff p j v t h⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

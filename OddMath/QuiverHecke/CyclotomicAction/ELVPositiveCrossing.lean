import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingHeight

/-! # The prescribed crossing with the positive polynomial window

The nonnegative KKO-height branch of the matrix in
`DeformedRouquierMatrix.md` is the actual cyclotomic crossing augmented by
the literal low polynomial columns. Its bijectivity follows from the proved
boundary division and the prescribed short-column diagram.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def positiveCrossingAssembly (j : {j : I // D.parity j = 1}) (v : List I) :
    (Source D Sc cutoff j.1 v v × boundaryRowWindow D Sc cutoff j v) →ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (v ++ [j.1]) :=
  (toCyclotomic D Sc cutoff j.1 v v).comp (LinearMap.fst k _ _) +
    (canonicalAppendTarget D Sc cutoff j.1 v (v ++ [j.1])).comp
      ((appendOutputEmbedding D Sc cutoff j.1 v v).comp
        ((boundaryRowWindow D Sc cutoff j v).subtype.comp (LinearMap.snd k _ _)))

@[simp] theorem positiveCrossingAssembly_apply (j : {j : I // D.parity j = 1})
    (v : List I) (s : Source D Sc cutoff j.1 v v)
    (r : boundaryRowWindow D Sc cutoff j v) :
    positiveCrossingAssembly D Sc cutoff j v (s, r) =
      toCyclotomic D Sc cutoff j.1 v v s +
        canonicalAppendTarget D Sc cutoff j.1 v (v ++ [j.1])
          (appendOutputEmbedding D Sc cutoff j.1 v v r) := rfl

theorem positiveCrossingAssembly_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (positiveCrossingAssembly D Sc cutoff j v) := by
  suffices hzero : ∀ z, positiveCrossingAssembly D Sc cutoff j v z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    rw [(positiveCrossingAssembly D Sc cutoff j v).map_sub, hxy, sub_self]
  rintro ⟨s, r⟩ hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v v s
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v v) y
  simp only [LinearMap.comp_apply] at hs
  have hm : shortCross D Sc cutoff j.1 v v y + appendOutputEmbedding D Sc cutoff j.1 v v r ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (v ++ [j.1])) := by
    rw [LinearMap.mem_ker, map_add, hs]
    exact hz
  rw [ker_canonicalAppendTarget] at hm
  obtain ⟨x, hx⟩ := hm
  have hc : appendC0 D Sc cutoff j.1 v v (shortCross D Sc cutoff j.1 v v y) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff j.1 v v
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨y, rfl⟩
  have hb : outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v x) = r := by
    rw [← appendC0_pMap D Sc cutoff p j v, hx, map_add, hc, appendC0_embedding, zero_add]
  have hrcoord : (boundaryPositiveEquiv D Sc cutoff p j v h).symm r = (0, r) := by
    apply (boundaryPositiveEquiv D Sc cutoff p j v h).injective
    rw [LinearEquiv.apply_symm_apply, boundaryPositiveEquiv_apply, map_zero, zero_add]
  have hr : r = 0 := by
    have he := congrArg (fun z => ((boundaryPositiveEquiv D Sc cutoff p j v h).symm z).2) hb
    rw [boundaryPositiveEquiv_symm_boundary, hrcoord] at he
    exact he.symm
  apply Prod.ext
  · change q D Sc cutoff j.1 v v y = 0
    apply toCyclotomic_injective_of_nonnegative_height D Sc cutoff p j v h
    have hz' : toCyclotomic D Sc cutoff j.1 v v (q D Sc cutoff j.1 v v y) = 0 := by
      simpa only [positiveCrossingAssembly_apply, hr, ZeroMemClass.coe_zero, map_zero, add_zero] using hz
    exact hz'.trans ((toCyclotomic D Sc cutoff j.1 v v).map_zero.symm)
  · exact hr

theorem positiveCrossingAssembly_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Surjective (positiveCrossingAssembly D Sc cutoff j v) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j.1 v (v ++ [j.1]) n
  obtain ⟨⟨f, r⟩, hfr⟩ := (boundaryPositiveAssembly_bijective D Sc cutoff p j v h).2
    (appendC0 D Sc cutoff j.1 v v z)
  change outputPolynomialBoundary D Sc cutoff p j v f + r =
    appendC0 D Sc cutoff j.1 v v z at hfr
  let x := sourceLongSection D Sc cutoff p j.1 v f
  have hc : z - pMap D Sc cutoff j.1 v (v ++ [j.1]) x -
      appendOutputEmbedding D Sc cutoff j.1 v v r ∈ appendCrossingSpan D Sc cutoff j.1 v v := by
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, map_sub, appendC0_pMap,
      appendC0_embedding]
    dsimp only [x]
    rw [outputLongExtraction_sourceLongSection, ← hfr]
    abel
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(q D Sc cutoff j.1 v v y, r), ?_⟩
  rw [positiveCrossingAssembly_apply]
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v v) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub, map_sub]
  have hx : pMap D Sc cutoff j.1 v (v ++ [j.1]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (v ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx]
  abel

/-- The literal crossing and low polynomial columns form the positive branch. -/
def positiveCrossingEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    (Source D Sc cutoff j.1 v v × boundaryRowWindow D Sc cutoff j v) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (v ++ [j.1]) :=
  LinearEquiv.ofBijective (positiveCrossingAssembly D Sc cutoff j v)
    ⟨positiveCrossingAssembly_injective D Sc cutoff p j v h,
      positiveCrossingAssembly_surjective D Sc cutoff p j v h⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryKernel

/-! # Even positive-height crossing and polynomial columns

The nonnegative-height branch of DeformedRouquierMatrix, section 4, uses
the prescribed balanced crossing plus literal low polynomial columns.
The actual even degree-shift division and separation prove its inverse on
arbitrary old Hom endpoints, without repeating coefficient elimination.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenPositiveCrossingAssembly (i : I) (v t : List I) :
    (Source D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) →ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (toCyclotomic D Sc cutoff i v t).comp (LinearMap.fst k _ _) +
    (canonicalAppendTarget D Sc cutoff i v (t ++ [i])).comp
      ((appendOutputEmbedding D Sc cutoff i v t).comp
        ((evenBoundaryRowWindow D Sc cutoff i v t).subtype.comp (LinearMap.snd k _ _)))

@[simp] theorem evenPositiveCrossingAssembly_apply (i : I)
    (v t : List I) (s : Source D Sc cutoff i v t)
    (r : evenBoundaryRowWindow D Sc cutoff i v t) :
    evenPositiveCrossingAssembly D Sc cutoff i v t (s, r) =
      toCyclotomic D Sc cutoff i v t s +
        canonicalAppendTarget D Sc cutoff i v (t ++ [i])
          (appendOutputEmbedding D Sc cutoff i v t r) := rfl

theorem evenPositiveCrossingAssembly_injective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I)
    (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    Function.Injective (evenPositiveCrossingAssembly D Sc cutoff i v t) := by
  suffices hzero : ∀ z, evenPositiveCrossingAssembly D Sc cutoff i v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : evenPositiveCrossingAssembly D Sc cutoff i v t (x - y) = evenPositiveCrossingAssembly D Sc cutoff i v t x - evenPositiveCrossingAssembly D Sc cutoff i v t y :=
      map_sub (evenPositiveCrossingAssembly D Sc cutoff i v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  rintro ⟨s, r⟩ hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff i v t s
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff i v t) y
  simp only [LinearMap.comp_apply] at hs
  have hm : shortCross D Sc cutoff i v t y + appendOutputEmbedding D Sc cutoff i v t r ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) := by
    rw [LinearMap.mem_ker, map_add, hs]
    exact hz
  rw [ker_canonicalAppendTarget] at hm
  obtain ⟨x, hx⟩ := hm
  have hc : appendC0 D Sc cutoff i v t (shortCross D Sc cutoff i v t y) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff i v t
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨y, rfl⟩
  have hb : offDiagonalPolynomialBoundary D Sc cutoff p i v t
      (offDiagonalLongExtraction D Sc cutoff p i v t x) = r := by
    rw [← appendC0_pMap_offDiagonal D Sc cutoff p i v t, hx, map_add, hc, appendC0_embedding, zero_add]
  have hr : r = 0 := by
    have hzrow : offDiagonalPolynomialBoundary D Sc cutoff p i v t
        (offDiagonalLongExtraction D Sc cutoff p i v t x) + -(r.val) = 0 := by
      rw [hb, add_neg_cancel]
    have hh := OddMath.Algebra.DegreeShiftRow.separation
      (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
      (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
      (outputSDegree D i v) (endpointQPDegree D cutoff i v)
      (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
      (offDiagonalBoundary_even_top D Sc cutoff p i hi v t)
      (offDiagonalLongExtraction D Sc cutoff p i v t x) (-r.val)
      (fun d _ => by omega)
      (fun n hn => by
        apply r.property
        change n ∈ r.val.support
        simpa only [Finsupp.support_neg] using hn) hzrow
    exact Subtype.ext (neg_eq_zero.mp hh.2)
  apply Prod.ext
  · change q D Sc cutoff i v t y = 0
    apply evenToCyclotomic_injective_of_nonnegative_height D Sc cutoff p i hi v t h
    have hz' : toCyclotomic D Sc cutoff i v t (q D Sc cutoff i v t y) = 0 := by
      simpa only [evenPositiveCrossingAssembly_apply, hr, ZeroMemClass.coe_zero, map_zero, add_zero] using hz
    exact hz'.trans ((toCyclotomic D Sc cutoff i v t).map_zero.symm)
  · exact hr

theorem evenPositiveCrossingAssembly_surjective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I)
    :
    Function.Surjective (evenPositiveCrossingAssembly D Sc cutoff i v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [i]) n
  let row := (evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t).symm
    (appendC0 D Sc cutoff i v t z)
  let f := row.1.val
  let r := row.2
  have hfr : offDiagonalPolynomialBoundary D Sc cutoff p i v t f + r.val =
      appendC0 D Sc cutoff i v t z := by
    exact (evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t).apply_symm_apply _
  let x := offDiagonalSourceLongSection D Sc cutoff p i v t f
  have hc : z - pMap D Sc cutoff i v (t ++ [i]) x -
      appendOutputEmbedding D Sc cutoff i v t r ∈ appendCrossingSpan D Sc cutoff i v t := by
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, map_sub, appendC0_pMap_offDiagonal,
      appendC0_embedding]
    dsimp only [x]
    rw [offDiagonalLongExtraction_sourceLongSection, ← hfr]
    abel
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(q D Sc cutoff i v t y, r), ?_⟩
  rw [evenPositiveCrossingAssembly_apply]
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff i v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub, map_sub]
  have hx : pMap D Sc cutoff i v (t ++ [i]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx]
  abel

/-- The literal crossing and low polynomial columns form the positive branch. -/
def evenPositiveCrossingEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    (Source D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  LinearEquiv.ofBijective (evenPositiveCrossingAssembly D Sc cutoff i v t)
    ⟨evenPositiveCrossingAssembly_injective D Sc cutoff p i hi v t h,
      evenPositiveCrossingAssembly_surjective D Sc cutoff p i hi v t⟩

/-- The polynomial complement is literally the coefficient window below the height. -/
theorem evenBoundaryRowWindow_eq_height (i : I) (v t : List I) (a : ℕ)
    (ha : endpointQPDegree D cutoff i v = outputSDegree D i v + a) :
    evenBoundaryRowWindow D Sc cutoff i v t =
      Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio a) := by
  unfold evenBoundaryRowWindow OddMath.Algebra.DegreeShiftRow.window
  congr 1
  ext n
  change (n + outputSDegree D i v < endpointQPDegree D cutoff i v) ↔ n < a
  omega

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor


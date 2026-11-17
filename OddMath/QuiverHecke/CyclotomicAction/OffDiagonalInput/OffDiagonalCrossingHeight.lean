import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.Algebra.LowPolynomialCoordinates
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalLong.OffDiagonalBoundaryLeading

/-!
# Off diagonal input

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Height consequences for the prescribed cyclotomic crossing

The polynomial boundary and actual short-column square give injectivity in
nonnegative KKO height and surjectivity in nonpositive KKO height. These are
diagram chases on the prescribed balanced source, not assumed snake data.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The prescribed crossing with the positive polynomial window

The nonnegative KKO-height branch of the matrix in
`DeformedRouquierMatrix.md` is the actual cyclotomic crossing augmented by
the literal low polynomial columns. Its bijectivity follows from the proved
arbitrary-Hom boundary division and the prescribed short-column diagram.
The old source and target words are independent.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The actual boundary-kernel map into the prescribed crossing source

The kernel arrow in the snake sequence of `DeformedRouquierMatrix.md` is
constructed from the existing source section, P map and short-cross decoder.
Its image is the kernel of the actual cyclotomic crossing. No exact-sequence
or faithful-action hypothesis is supplied. The construction and exactness
are valid for every moving colour; parity enters the subsequent row and cap
normal forms rather than this snake comparison.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalShortCross_decode_of_mem (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i]))
    (hz : z ∈ appendCrossingSpan D Sc cutoff i v t) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) = z := by
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, rfl⟩ := hz
  rw [ShortCrossCoordinates.decode_shortCross]

def offDiagonalBoundarySnake (p : ZMod 2) (j : I) (v t : List I) :
    LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t) →ₗ[k]
      Source D Sc cutoff j v t :=
  q D Sc cutoff j v t ∘ₗ ShortCrossCoordinates.decode D Sc cutoff j v t ∘ₗ
    pMap D Sc cutoff j v (t ++ [j]) ∘ₗ offDiagonalSourceLongSection D Sc cutoff p j v t ∘ₗ
      (LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t)).subtype

theorem offDiagonalBoundarySnake_lift (p : ZMod 2) (j : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t)) :
    shortCross D Sc cutoff j v t
      (ShortCrossCoordinates.decode D Sc cutoff j v t
        (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f))) =
      pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f) := by
  apply offDiagonalShortCross_decode_of_mem
  rw [← appendC0_ker, LinearMap.mem_ker, appendC0_pMap_offDiagonal,
    offDiagonalLongExtraction_sourceLongSection]
  exact f.property

theorem offDiagonalToCyclotomic_boundarySnake (p : ZMod 2)
    (j : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t)) :
    toCyclotomic D Sc cutoff j v t (offDiagonalBoundarySnake D Sc cutoff p j v t f) = 0 := by
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t)
    (ShortCrossCoordinates.decode D Sc cutoff j v t
      (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f)))
  simp only [LinearMap.comp_apply] at hs
  change _ = toCyclotomic D Sc cutoff j v t (offDiagonalBoundarySnake D Sc cutoff p j v t f) at hs
  rw [← hs, offDiagonalBoundarySnake_lift]
  have hm : pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f) ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨_, rfl⟩
  exact hm

theorem offDiagonalBoundarySnake_injective (p : ZMod 2)
    (j : I) (v t : List I) :
    Function.Injective (offDiagonalBoundarySnake D Sc cutoff p j v t) := by
  suffices hzero : ∀ z, offDiagonalBoundarySnake D Sc cutoff p j v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : offDiagonalBoundarySnake D Sc cutoff p j v t (x - y) = offDiagonalBoundarySnake D Sc cutoff p j v t x - offDiagonalBoundarySnake D Sc cutoff p j v t y :=
      map_sub (offDiagonalBoundarySnake D Sc cutoff p j v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  intro f hf
  have hy : ShortCrossCoordinates.decode D Sc cutoff j v t
      (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f)) ∈
      LinearMap.ker (q D Sc cutoff j v t) := hf
  rw [← range_pprime_eq_ker_q] at hy
  obtain ⟨a, ha⟩ := hy
  have he : alpha D Sc cutoff j v t a = offDiagonalSourceLongSection D Sc cutoff p j v t f := by
    apply pMap_injective D Sc cutoff j v (t ++ [j])
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.trans (by rw [ha, offDiagonalBoundarySnake_lift])
  have hb := congrArg (offDiagonalLongExtraction D Sc cutoff p j v t) he
  rw [offDiagonalLongExtraction_alpha, offDiagonalLongExtraction_sourceLongSection] at hb
  exact Subtype.ext hb.symm

/-- Changing the source lift by its prescribed short coordinate does not
change the cyclotomic snake class. This permits using the original corrected
rho lifts in subsequent cap recurrences. -/
theorem offDiagonalBoundarySnake_eq_lift (p : ZMod 2)
    (j : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t))
    (z : Target D Sc cutoff j v (t ++ [j]))
    (hz : offDiagonalLongExtraction D Sc cutoff p j v t z = f) :
    offDiagonalBoundarySnake D Sc cutoff p j v t f =
      q D Sc cutoff j v t (ShortCrossCoordinates.decode D Sc cutoff j v t
        (pMap D Sc cutoff j v (t ++ [j]) z)) := by
  have he := offDiagonalSource_reconstruction D Sc cutoff p j v t z
  rw [hz] at he
  rw [← he, map_add]
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t)
    (extract D Sc cutoff j v t z)
  simp only [LinearMap.comp_apply] at hs
  rw [hs, map_add, ShortCrossCoordinates.decode_shortCross, map_add]
  have hq : q D Sc cutoff j v t
      (pprime D Sc cutoff j v t (extract D Sc cutoff j v t z)) = 0 := by
    have hm : pprime D Sc cutoff j v t (extract D Sc cutoff j v t z) ∈
        LinearMap.ker (q D Sc cutoff j v t) := by
      rw [← range_pprime_eq_ker_q]
      exact ⟨_, rfl⟩
    exact hm
  rw [hq, zero_add]
  rfl

theorem offDiagonalRange_boundarySnake (p : ZMod 2)
    (j : I) (v t : List I) :
    LinearMap.range (offDiagonalBoundarySnake D Sc cutoff p j v t) =
      LinearMap.ker (toCyclotomic D Sc cutoff j v t) := by
  apply le_antisymm
  · rintro z ⟨f, rfl⟩
    exact offDiagonalToCyclotomic_boundarySnake D Sc cutoff p j v t f
  · intro z hz
    obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j v t z
    have hy : shortCross D Sc cutoff j v t y ∈
        LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
      rw [LinearMap.mem_ker]
      have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
      exact he.trans hz
    rw [ker_canonicalAppendTarget] at hy
    obtain ⟨x, hx⟩ := hy
    have hc : appendC0 D Sc cutoff j v t (shortCross D Sc cutoff j v t y) = 0 := by
      apply appendCrossingSpan_le_ker D Sc cutoff j v t
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    let f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t) :=
      ⟨offDiagonalLongExtraction D Sc cutoff p j v t x, by
        rw [LinearMap.mem_ker, ← appendC0_pMap_offDiagonal D Sc cutoff p j v t, hx]
        exact hc⟩
    let a := extract D Sc cutoff j v t x
    have he : y = pprime D Sc cutoff j v t a +
        ShortCrossCoordinates.decode D Sc cutoff j v t
          (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f)) := by
      apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j v t
      rw [map_add, offDiagonalBoundarySnake_lift]
      have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
      simp only [LinearMap.comp_apply] at hs
      rw [← hs, ← map_add, offDiagonalSource_reconstruction, hx]
    refine ⟨f, ?_⟩
    have hqa : q D Sc cutoff j v t (pprime D Sc cutoff j v t a) = 0 := by
      have hm : pprime D Sc cutoff j v t a ∈ LinearMap.ker (q D Sc cutoff j v t) := by
        rw [← range_pprime_eq_ker_q]
        exact ⟨a, rfl⟩
      exact hm
    rw [he, map_add, hqa, zero_add]
    rfl

/-- The actual kernel of the prescribed cyclotomic crossing is the boundary kernel. -/
def offDiagonalBoundarySnakeKernelEquiv (p : ZMod 2)
    (j : I) (v t : List I) :
    LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff j v t) :=
  LinearEquiv.ofBijective
    ((offDiagonalBoundarySnake D Sc cutoff p j v t).codRestrict _
      (fun f => offDiagonalToCyclotomic_boundarySnake D Sc cutoff p j v t f))
    ⟨fun f g hfg => offDiagonalBoundarySnake_injective D Sc cutoff p j v t (congrArg Subtype.val hfg),
      by
        intro z
        have hz : z.1 ∈ LinearMap.range (offDiagonalBoundarySnake D Sc cutoff p j v t) := by
          rw [offDiagonalRange_boundarySnake]
          exact z.property
        obtain ⟨f, hf⟩ := hz
        exact ⟨f, Subtype.ext hf⟩⟩

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
